-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhPos_term_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:44:27.163026+00:00
-- url     : https://prove2.me/submissions/f5d9977c-bae7-415c-8f36-7d9bcd02deaf

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHSt
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_Positivity
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPos
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhPos_term
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhPos_term_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (h1 : χ₁ ^ 2 = 1)
    (k : ℕ) (σ γ : ℝ) (n : ℕ) :
    0 ≤ (term (logMul^[k] (↗(1 : DirichletCharacter ℂ q) * ↗Λ)) (σ : ℂ) n).re
      + (term (logMul^[k] (↗χ₁ * ↗Λ)) (σ : ℂ) n).re
      + (term (logMul^[k] (↗χ * ↗Λ)) ((σ : ℂ) + γ * I) n).re
      + (term (logMul^[k] (↗(χ * χ₁) * ↗Λ)) ((σ : ℂ) + γ * I) n).re := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [dhPos_term_real, dhPos_term_real, dhPos_term, dhPos_term]
  simp only [Complex.re_ofReal_mul]
  have hA0 : 0 ≤ (Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) :=
    mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k)
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
  have hz1 : ‖(n : ℂ) ^ ((γ : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    simp
  have hw : -1 ≤ (χ n / (n : ℂ) ^ ((γ : ℂ) * I)).re := by
    have hnorm : ‖χ n / (n : ℂ) ^ ((γ : ℂ) * I)‖ ≤ 1 := by
      rw [norm_div, hz1, div_one]
      exact DirichletCharacter.norm_le_one χ _
    have h2 := Complex.abs_re_le_norm (χ n / (n : ℂ) ^ ((γ : ℂ) * I))
    linarith [(abs_le.1 h2).1]
  have key : 0 ≤ ((1 : DirichletCharacter ℂ q) n).re + (χ₁ n).re + (χ n / (n : ℂ) ^ ((γ : ℂ) * I)).re +
      ((χ * χ₁) n / (n : ℂ) ^ ((γ : ℂ) * I)).re := by
    by_cases hu : IsUnit (n : ZMod q)
    · have h1n : (1 : DirichletCharacter ℂ q) n = 1 := MulChar.one_apply hu
      have hsq : χ₁ n * χ₁ n = 1 := by
        have e := congrArg (fun ψ : DirichletCharacter ℂ q => ψ n) h1
        simpa only [pow_two, MulChar.mul_apply, MulChar.one_apply hu] using e
      have hχ₁ : χ₁ n = 1 ∨ χ₁ n = -1 := by
        have h' : (χ₁ n - 1) * (χ₁ n + 1) = 0 := by linear_combination hsq
        rcases mul_eq_zero.1 h' with h | h
        · left
          linear_combination h
        · right
          linear_combination h
      rw [MulChar.mul_apply, h1n]
      rcases hχ₁ with h | h
      · rw [h, mul_one]
        simp only [Complex.one_re]
        linarith
      · rw [h]
        simp only [Complex.one_re, Complex.neg_re, mul_neg, mul_one, neg_div]
        linarith
    · have h0 : ∀ ψ : DirichletCharacter ℂ q, ψ n = 0 := fun ψ => MulChar.map_nonunit ψ hu
      simp [h0]
  nlinarith [mul_nonneg hA0 key]
end Formalism.HermitianLattices.Ext.PrimesInProgressions
