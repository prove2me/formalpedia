-- Prove2me | solution 1 for BookProof.ChapterSphericalPlancherel.fourier_odd_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:28:55.539591+00:00
-- url     : https://prove2.me/submissions/197806da-b04f-4edc-92a5-4815687306c9

-- Generated from ChapterSphericalPlancherel.lean — solution of BookProof.ChapterSphericalPlancherel.fourier_odd_eq
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
import Theorems.Thm_BookProof_ChapterSphericalPlancherel_integral_eq_zero_of_odd
import Theorems.Thm_BookProof_ChapterSphericalPlancherel_integral_eq_two_smul_of_even
import Theorems.Thm_BookProof_ChapterSphericalPlancherel_integrable_bdd_mul
import Theorems.Thm_BookProof_ChapterSphericalPlancherel_fourier_eq_cos_sub_sin
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalPlancherel




open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (G : ℝ → ℂ) (hG : Integrable G) (hodd : ∀ x, G (-x) = -G x) (w : ℝ) :
    𝓕 G w = -(2 * Complex.I) * sineTransform G w := by

  have hA : Integrable (fun x : ℝ => (Real.cos (2 * π * (x * w)) : ℂ) * G x) :=
    integrable_bdd_mul G hG _ (by fun_prop) fun x => Real.abs_cos_le_one _
  have hB : Integrable (fun x : ℝ => (Real.sin (2 * π * (x * w)) : ℂ) * G x) :=
    integrable_bdd_mul G hG _ (by fun_prop) fun x => Real.abs_sin_le_one _
  rw [fourier_eq_cos_sub_sin]
  have hrw : (fun x : ℝ => ((Real.cos (2 * π * (x * w)) : ℂ)
      - (Real.sin (2 * π * (x * w)) : ℂ) * Complex.I) * G x)
      = fun x : ℝ => ((Real.cos (2 * π * (x * w)) : ℂ) * G x)
        + (-Complex.I) * ((Real.sin (2 * π * (x * w)) : ℂ) * G x) := by
    funext x; ring
  rw [hrw, integral_add hA (hB.const_mul _), integral_const_mul]
  have h0 : ∫ x : ℝ, (Real.cos (2 * π * (x * w)) : ℂ) * G x = 0 := by
    refine integral_eq_zero_of_odd _ fun x => ?_
    rw [hodd, show 2 * π * (-x * w) = -(2 * π * (x * w)) by ring, Real.cos_neg]
    ring
  have h2 : ∫ x : ℝ, (Real.sin (2 * π * (x * w)) : ℂ) * G x = (2 : ℝ) • sineTransform G w := by
    refine integral_eq_two_smul_of_even _ (fun x => ?_) hB
    rw [hodd, show 2 * π * (-x * w) = -(2 * π * (x * w)) by ring, Real.sin_neg]
    push_cast; ring
  rw [h0, h2, Complex.real_smul]
  push_cast
  ring
