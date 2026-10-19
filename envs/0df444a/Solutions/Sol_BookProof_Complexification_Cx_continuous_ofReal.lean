-- Prove2me | solution 1 for BookProof.Complexification.Cx.continuous_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:23:19.283957+00:00
-- url     : https://prove2.me/submissions/3840fcb8-2f52-4222-bb4e-b4e470c8e873

-- Generated from ChapterA1b.lean — solution of BookProof.Complexification.Cx.continuous_ofReal
import Mathlib
import Definitions.Def_ChapterA1b
import Definitions.Def_ChapterA
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_Complexification
open BookProof.Complexification
open BookProof.Complexification.Cx



open scoped RealInnerProductSpace
open BookProof.ChapterA
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData


variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

set_option maxHeartbeats 1000000 in
theorem solution : Continuous (Cx.ofReal : W → Cx W) := by

  refine LipschitzWith.continuous (K := 1) ?_
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have : ofReal x - ofReal y = ofReal (x - y) := by ext <;> simp
  rw [this]
  rw [← Real.sqrt_sq (norm_nonneg (ofReal (x - y))), ← Real.sqrt_sq (norm_nonneg (x - y))]
  rw [norm_sq]; simp
