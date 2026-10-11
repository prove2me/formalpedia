-- Prove2me | solution 1 for BookProof.ChapterShannonSampling.bandSignal_sample
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:32:33.287504+00:00
-- url     : https://prove2.me/submissions/8fb33765-ea0e-45e5-a7aa-0327f43fb2b0

-- Generated from ChapterShannonSampling.lean — solution of BookProof.ChapterShannonSampling.bandSignal_sample
import Mathlib
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterShannonSampling




open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

set_option maxHeartbeats 1000000 in
theorem solution (F : AddCircle T → ℂ) (n : ℤ) :
    bandSignal (T := T) F (-(n / T)) = (T : ℂ) * fourierCoeff F n := by

  have hT0 : (0 : ℝ) < T := hT.out
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
  have hpt : ∀ ξ : ℝ, Complex.exp (2 * π * I * ((-((n : ℝ) / T) : ℝ) : ℂ) * ξ) * F ξ
      = (fourier (-n) (ξ : AddCircle T)) • F ξ := by
    intro ξ
    rw [fourier_coe_apply, smul_eq_mul]
    congr 2
    push_cast
    field_simp
  rw [fourierCoeff_eq_intervalIntegral _ n (-(T / 2)), bandSignal,
    show -(T / 2) + T = T / 2 from by ring]
  rw [intervalIntegral.integral_congr (fun ξ _ => hpt ξ)]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
  field_simp
