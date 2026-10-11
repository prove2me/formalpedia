-- Prove2me | solution 1 for BookProof.ChapterSphericalPlancherel.fourier_eq_cos_sub_sin
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:28:54.334988+00:00
-- url     : https://prove2.me/submissions/00b641f2-4273-4a22-a4ae-4393a7b5cec9

-- Generated from ChapterSphericalPlancherel.lean — solution of BookProof.ChapterSphericalPlancherel.fourier_eq_cos_sub_sin
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalPlancherel




open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (f : ℝ → ℂ) (w : ℝ) :
    𝓕 f w = ∫ x : ℝ, ((Real.cos (2 * π * (x * w)) : ℂ)
      - (Real.sin (2 * π * (x * w)) : ℂ) * Complex.I) * f x := by

  rw [Real.fourier_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [RCLike.inner_apply, conj_trivial]
  rw [show ((𝐞 (-(w * v))) • f v) = (𝐞 (-(w * v)) : ℂ) * f v from rfl, Real.fourierChar_apply,
    show ((2 * π * -(w * v) : ℝ) : ℂ) * Complex.I
        = ((-(2 * π * (v * w)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring
