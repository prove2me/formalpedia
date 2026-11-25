-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhDom_term_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:30:09.056011+00:00
-- url     : https://prove2.me/submissions/a457d626-e68e-41f9-a96f-a72b74327106

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPos
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHDom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Complex Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation
private theorem logMul_iterate_apply_eq_log_pow_mul (f : ℕ → ℂ) (k n : ℕ) :
    logMul^[k] f n = Complex.log n ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', logMul, ih]
    ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

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
    ‖term (logMul^[k] (↗χ * ↗Λ)) ((σ : ℂ) + γ * I) n
      + term (logMul^[k] (↗(χ * χ₁) * ↗Λ)) ((σ : ℂ) + γ * I) n‖ ≤
    (term (logMul^[k] (↗(1 : DirichletCharacter ℂ q) * ↗Λ)) (σ : ℂ) n).re
      + (term (logMul^[k] (↗χ₁ * ↗Λ)) (σ : ℂ) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  set A : ℝ := Real.log n ^ k * Λ n with hA
  have hA0 : 0 ≤ A :=
    mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k) ArithmeticFunction.vonMangoldt_nonneg
  have e1 : ∀ c : ℂ, Complex.log n ^ k * (c * ((Λ n : ℝ) : ℂ)) = (A : ℂ) * c := by
    intro c
    rw [hA, ← Complex.natCast_log]
    push_cast
    ring
  have hN : ‖(n : ℂ) ^ ((σ : ℂ) + γ * I)‖ = (n : ℝ) ^ σ := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    simp
  have hR : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hnpos.le]
  have hp : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hnpos σ
  have hre : ∀ c : ℝ, ((A : ℂ) * (c : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)).re = A * c / (n : ℝ) ^ σ := by
    intro c
    rw [← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
  simp only [term_of_ne_zero hn, logMul_iterate_apply_eq_log_pow_mul, Pi.mul_apply, MulChar.coeToFun_mul, e1, hR]
  by_cases hu : IsUnit (n : ZMod q)
  · obtain ⟨u, hu'⟩ := hu
    rw [← hu', MulChar.one_apply_coe]
    have hχ : ‖χ u‖ = 1 := DirichletCharacter.unit_norm_eq_one χ u
    have h1u : χ₁ u * χ₁ u = 1 := by
      rw [← pow_two, ← MulChar.pow_apply_coe, h1, MulChar.one_apply_coe]
    rcases mul_self_eq_one_iff.mp h1u with h | h
    · rw [h]
      have := hre 1
      push_cast at this
      rw [this]
      have e2 : (A : ℂ) * χ u / (n : ℂ) ^ ((σ : ℂ) + γ * I) + (A : ℂ) * (χ u * 1) /
          (n : ℂ) ^ ((σ : ℂ) + γ * I) = ((2 * A : ℝ) : ℂ) * χ u / (n : ℂ) ^ ((σ : ℂ) + γ * I) := by
        push_cast
        ring
      rw [e2, norm_div, norm_mul, hχ, hN, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      apply le_of_eq
      ring
    · rw [h]
      have := hre 1
      have h' := hre (-1)
      push_cast at this h'
      rw [this, h']
      have e2 : (A : ℂ) * χ u / (n : ℂ) ^ ((σ : ℂ) + γ * I) + (A : ℂ) * (χ u * -1) /
          (n : ℂ) ^ ((σ : ℂ) + γ * I) = 0 := by
        ring
      rw [e2, norm_zero]
      apply le_of_eq
      ring
  · simp [MulChar.map_nonunit _ hu]
end Formalism.HermitianLattices.Ext.PrimesInProgressions
