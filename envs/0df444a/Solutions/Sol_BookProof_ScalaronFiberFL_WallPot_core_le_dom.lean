-- Prove2me | solution 1 for BookProof.ScalaronFiberFL.WallPot.core_le_dom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-22T18:09:56.881582+00:00
-- url     : https://prove2.me/submissions/fd4a7663-68a0-4ff6-b1b9-019895e7183a

-- Generated from ChapterScalaronFiberFL.lean — solution of BookProof.ScalaronFiberFL.WallPot.core_le_dom
import Mathlib
import Definitions.Def_ChapterScalaronFiberFL
import Theorems.Thm_BookProof_QgOuterFockFL_friedrichsComparison_extends
import Theorems.Thm_BookProof_ScalaronEsa_ccDomain_dense
open BookProof.ScalaronFiberFL
open BookProof.ScalaronFiberFL.WallPot




open MeasureTheory SchwartzMap
open BookProof.StrichartzWave
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallEsaSemibounded BookProof.WallEsaBddBelow
open BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.SchrodingerCutoff BookProof.FriedrichsExtension

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (W : WallPot) (s : ℝ)
variable (W : WallPot) (s : ℝ) (hs : 0 ≤ s)

set_option maxHeartbeats 1000000 in
theorem solution : ccDomain ℝ ≤ (W.comparison s hs).dom :=
  fun v hv =>
    (friedrichsComparison_extends (W.posSym s hs) ccDomain_dense ⟨v, hv⟩).choose
