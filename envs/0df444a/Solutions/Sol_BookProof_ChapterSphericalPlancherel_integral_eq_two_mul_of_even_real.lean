-- Prove2me | solution 1 for BookProof.ChapterSphericalPlancherel.integral_eq_two_mul_of_even_real
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:28:50.59699+00:00
-- url     : https://prove2.me/submissions/b02be15e-06ee-40f4-be5f-5100daf84382

-- Generated from ChapterSphericalPlancherel.lean — solution of BookProof.ChapterSphericalPlancherel.integral_eq_two_mul_of_even_real
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalPlancherel




open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (h : ℝ → ℝ) (he : ∀ x, h (-x) = h x) :
    ∫ x : ℝ, h x = 2 * ∫ x in Ioi (0 : ℝ), h x := by

  rw [← integral_comp_abs (f := h)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [h1]
  · rw [h1, he]
