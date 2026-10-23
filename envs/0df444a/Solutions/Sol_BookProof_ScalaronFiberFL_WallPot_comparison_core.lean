-- Prove2me | solution 1 for BookProof.ScalaronFiberFL.WallPot.comparison_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-22T18:07:10.212676+00:00
-- url     : https://prove2.me/submissions/d8e61cc5-0de8-4e87-b35f-1ca0d094e35e

-- Generated from ChapterScalaronFiberFL.lean — solution of BookProof.ScalaronFiberFL.WallPot.comparison_core
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
theorem solution (p : ccDomain ℝ) (h : (p : L2R) ∈ (W.comparison s hs).dom) :
    (W.comparison s hs).op ⟨(p : L2R), h⟩ = W.ham s p := (friedrichsComparison_extends (W.posSym s hs) ccDomain_dense p).choose_spec
