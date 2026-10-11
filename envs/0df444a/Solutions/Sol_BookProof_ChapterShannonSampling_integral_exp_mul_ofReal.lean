-- Prove2me | solution 1 for BookProof.ChapterShannonSampling.integral_exp_mul_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:31:05.642006+00:00
-- url     : https://prove2.me/submissions/ac95e97d-d9d7-4a7c-9120-d53757fdb556

-- Generated from ChapterShannonSampling.lean — solution of BookProof.ChapterShannonSampling.integral_exp_mul_ofReal
import Mathlib
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterShannonSampling




open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (T a : ℝ) (hT : 0 < T) :
    (∫ ξ in (-(T / 2))..(T / 2), Complex.exp (2 * π * I * a * ξ))
      = (T : ℂ) * (sinc (a * T) : ℝ) := by

  rcases eq_or_ne a 0 with rfl | ha
  · simp [sinc]
  · have hc : (2 * π * I * a : ℂ) ≠ 0 := by simp [Complex.ext_iff, Real.pi_ne_zero, ha]
    rw [integral_exp_mul_complex hc]
    have haT : a * T ≠ 0 := mul_ne_zero ha hT.ne'
    have hsinc : (sinc (a * T) : ℂ) = (Real.sin (π * (a * T)) : ℂ) / ((π : ℂ) * (a * T)) := by
      rw [sinc, if_neg haT]; push_cast; ring
    rw [hsinc]
    have h1 : (2 * (π : ℂ) * I * a * ((T / 2 : ℝ) : ℂ)) = ((π * (a * T) : ℝ) : ℂ) * I := by
      push_cast; ring
    have h2 : (2 * (π : ℂ) * I * a * ((-(T / 2) : ℝ) : ℂ)) = -(((π * (a * T) : ℝ) : ℂ) * I) := by
      push_cast; ring
    rw [h1, h2]
    set z : ℂ := ((π * (a * T) : ℝ) : ℂ) with hz
    have hsin : Complex.exp (z * I) - Complex.exp (-(z * I)) = 2 * I * Complex.sin z := by
      rw [Complex.sin]; ring_nf; rw [Complex.I_sq]; ring
    rw [hsin, ← Complex.ofReal_sin]
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    field_simp
