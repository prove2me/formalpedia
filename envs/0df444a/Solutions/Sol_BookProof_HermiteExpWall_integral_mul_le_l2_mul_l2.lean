-- Prove2me | solution 1 for BookProof.HermiteExpWall.integral_mul_le_l2_mul_l2
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:05:48.974906+00:00
-- url     : https://prove2.me/submissions/655ba184-ef75-4bfc-9882-a4f62668dad6

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.integral_mul_le_l2_mul_l2
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteExpWall




open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (f g : ℝ → ℝ) (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) : ∫ x, ‖f x‖ * ‖g x‖ ≤ l2 f * l2 g := by

  have hc : Real.HolderConjugate 2 2 := by constructor <;> norm_num
  have h := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := volume) (f := f) (g := g) hc
    (by simpa using hf) (by simpa using hg)
  have hrw : ∀ u : ℝ → ℝ, (∫ x, ‖u x‖ ^ (2:ℝ)) ^ (1 / (2:ℝ)) = l2 u := by
    intro u
    rw [l2, Real.sqrt_eq_rpow]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [Real.norm_eq_abs]
  rw [hrw f, hrw g] at h
  exact h
