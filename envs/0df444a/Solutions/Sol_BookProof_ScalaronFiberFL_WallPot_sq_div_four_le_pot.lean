-- Prove2me | solution 1 for BookProof.ScalaronFiberFL.WallPot.sq_div_four_le_pot
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-03T04:43:56.359578+00:00
-- url     : https://prove2.me/submissions/5c4f9368-e2a2-4bac-86b5-6c2fb6a1c29c

-- Generated from ChapterScalaronFiberFL.lean — solution of BookProof.ScalaronFiberFL.WallPot.sq_div_four_le_pot
import Mathlib
import Definitions.Def_ChapterScalaronFiberFL
import Theorems.Thm_BookProof_ChapterDutchBook_Coherent_nonneg
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

set_option maxHeartbeats 1000000 in
theorem solution (hs : 0 ≤ s) (x : ℝ) : x ^ 2 / 4 ≤ W.pot s x := by

  have h2 := W.nonneg x
  simp only [pot]
  linarith
