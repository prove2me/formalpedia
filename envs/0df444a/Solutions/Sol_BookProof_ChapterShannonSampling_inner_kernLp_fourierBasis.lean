-- Prove2me | solution 1 for BookProof.ChapterShannonSampling.inner_kernLp_fourierBasis
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:32:32.144623+00:00
-- url     : https://prove2.me/submissions/4d4ee2f8-e483-4bde-b5e4-0c9adeec442a

-- Generated from ChapterShannonSampling.lean — solution of BookProof.ChapterShannonSampling.inner_kernLp_fourierBasis
import Mathlib
import Definitions.Def_ChapterShannonSampling
import Theorems.Thm_BookProof_ChapterShannonSampling_sinc_neg
import Theorems.Thm_BookProof_ChapterShannonSampling_integral_exp_mul_ofReal
open BookProof.ChapterShannonSampling




open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

set_option maxHeartbeats 1000000 in
theorem solution (x : ℝ) (n : ℤ) :
    inner ℂ (kernLp (T := T) x) (fourierBasis (T := T) n) = (sinc (T * x + n) : ℝ) := by

  have hT0 : (0 : ℝ) < T := hT.out
  have hcoeff : fourierCoeff (kern (T := T) x) n = (sinc (T * x + n) : ℝ) := by
    rw [fourierCoeff_eq_intervalIntegral _ n (-(T / 2))]
    have hint : (∫ ξ in (-(T / 2))..(-(T / 2) + T),
          (fourier (-n) (ξ : AddCircle T)) • kern (T := T) x ξ)
        = ∫ ξ in (-(T / 2))..(-(T / 2) + T),
            Complex.exp (2 * π * I * (-(x + n / T)) * ξ) := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun ξ hξ => ?_)
      have hξ' : ξ ∈ Ioc (-(T / 2)) (-(T / 2) + T) := by
        rwa [Set.uIoc_of_le (by linarith)] at hξ
      rw [kern_coe_apply x hξ', fourier_coe_apply, smul_eq_mul, ← Complex.exp_add]
      congr 1
      have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
      field_simp
      push_cast
      ring
    rw [hint]
    have hexp := integral_exp_mul_ofReal T (-(x + n / T)) hT0
    push_cast at hexp
    rw [show -(T / 2) + T = T / 2 by ring, hexp]
    have hsinc : sinc (-(x + n / T) * T) = sinc (T * x + n) := by
      rw [show -(x + (n : ℝ) / T) * T = -((x + (n : ℝ) / T) * T) by ring, sinc_neg]
      congr 1
      field_simp
    rw [hsinc]
    have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
    field_simp
  have h1 : inner ℂ (fourierBasis (T := T) n) (kernLp (T := T) x)
      = ((sinc (T * x + n) : ℝ) : ℂ) := by
    rw [← fourierBasis.repr_apply_apply, fourierBasis_repr]
    simp only [kernLp]
    rw [fourierCoeff_congr_ae (memLp_kern (T := T) x).coeFn_toLp, hcoeff]
  calc inner ℂ (kernLp (T := T) x) (fourierBasis (T := T) n)
      = conj (inner ℂ (fourierBasis (T := T) n) (kernLp (T := T) x)) := by
        rw [inner_conj_symm]
    _ = ((sinc (T * x + n) : ℝ) : ℂ) := by rw [h1]; simp
