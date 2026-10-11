-- Prove2me | solution 1 for BookProof.ChapterSphericalPlancherel.integral_eq_zero_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:28:48.293681+00:00
-- url     : https://prove2.me/submissions/d206edc5-f9a9-4c91-9816-88b973af6273

-- Generated from ChapterSphericalPlancherel.lean — solution of BookProof.ChapterSphericalPlancherel.integral_eq_zero_of_odd
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalPlancherel




open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (h : ∀ x, f (-x) = -f x) : ∫ x : ℝ, f x = 0 := by

  have h1 : ∫ x : ℝ, f (-x) = ∫ x : ℝ, f x := integral_neg_eq_self f volume
  simp_rw [h, integral_neg] at h1
  have h2 : (2 : ℝ) • (∫ x : ℝ, f x) = 0 := by
    rw [two_smul]; nth_rewrite 1 [← h1]; abel
  simpa using h2
