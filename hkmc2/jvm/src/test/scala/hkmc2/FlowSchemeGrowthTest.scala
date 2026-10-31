package hkmc2

import org.scalatest.funsuite.AnyFunSuite
import scala.collection.mutable.ArrayBuffer

import codegen.{Erasure, Lowering}
import codegen.flowAnalysis.{FlowAnalysis, FlowConstraintsCollector, FlowPreAnalyzer}
import semantics.{Elaborator, SymbolPrinter}
import utils.*, shorthands.*
import io.PlatformPath.given


/** Diff tests cover the resulting flows and rewrites. This checks the separate
  * work bound: adding local constraints to a polymorphic definition must not add
  * those constraints to the whole-program solver once for each instantiation.
  */
class FlowSchemeGrowthTest extends AnyFunSuite:
  private val cctx = TestFolders.compilerCtx(os.pwd)
  private given DebugPrinter = new DebugPrinter()
  private given TraceLogger = TraceLogger.silent

  private def queuedConstraints(aliases: Int, calls: Int, mono: Bool): Int =
    val dir = os.temp.dir(prefix = "flow-scheme-growth-")
    try
      val file = dir / "Growth.mls"
      val locals = (1 to aliases).map: i =>
        s"  let value$i = ${if i == 1 then "value" else s"value${i - 1}"}"
      val arguments = (1 to calls).map(i => s"identity($i)").mkString(", ")
      os.write(file,
        s"""private fun identity(value) =
           |${locals.mkString("\n")}
           |  value$aliases
           |fun use() = [$arguments]
           |""".stripMargin)
      val diagnostics = ArrayBuffer.empty[Diagnostic]
      given Raise = diagnostics += _
      val prelude = cctx.getPrelude(cctx.paths.preludeFile).ctx
      val artifact = cctx.getElaboratedBlock(file, prelude)
      val errors = diagnostics.collect { case error: ErrorReport => error }
      assert(errors.isEmpty, errors.map(_.theMsg).mkString("\n"))

      given Config = artifact.config
      given eState: Elaborator.State = artifact.state
      given Elaborator.Ctx = artifact.ctx
      given SymbolPrinter = new SymbolPrinter(Scope.empty(Scope.Cfg.default))
      given Erasure = Erasure(artifact.term)
      // Collect from freshly lowered source so simplification cannot remove the
      // alias chain before the flow-analysis work is measured.
      val program = new Lowering().program(artifact.term, Set.empty)
      given fState: FlowAnalysis.State = new FlowAnalysis.State
      val pre = new FlowPreAnalyzer(program)
      val collector = new FlowConstraintsCollector(pre,
        mono = mono, nonAffineTracking = false, accumulatorTracking = false)
      collector.allConstraints.size
    finally os.remove.all(dir)

  test("scheme-local constraints are not queued again for every use"):
    for calls <- List(1, 8) do
      val small = queuedConstraints(1, calls, mono = false)
      val large = queuedConstraints(64, calls, mono = false)
      withClue(s"$calls calls: $small constraints with 1 alias, $large with 64 aliases: "):
        assert(large == small,
          "The whole-program solve should connect solved schemes, without replaying their local constraints")

  test("mono references do not repeatedly import the same local bounds"):
    val smallSingle = queuedConstraints(1, 1, mono = true)
    val smallRepeated = queuedConstraints(1, 8, mono = true)
    val largeSingle = queuedConstraints(64, 1, mono = true)
    val largeRepeated = queuedConstraints(64, 8, mono = true)
    val smallIncrease = smallRepeated - smallSingle
    val largeIncrease = largeRepeated - largeSingle
    withClue(s"1 to 8 calls add $smallIncrease constraints with 1 alias, $largeIncrease with 64 aliases: "):
      assert(largeIncrease == smallIncrease,
        "Additional mono references should add caller connections without importing the same local bounds again")
