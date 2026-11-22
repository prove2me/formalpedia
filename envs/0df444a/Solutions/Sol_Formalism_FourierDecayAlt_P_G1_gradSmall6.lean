-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G1.gradSmall6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:20:00.157881+00:00
-- url     : https://prove2.me/submissions/bd5dee27-c25e-43d3-94d8-65c4ca23169a

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G1
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G1
theorem _root_.solution (m : ℕ) (D' : ℂ) (hD : D' ≠ 0) (x : Fin (m + 1) → ℂ) (hx : ∀ k, x k ≠ 0)
    (η : ℝ) (hη : 0 < η) (hη' : η ≤ 1 / (4 * ((m : ℝ) + 2))) (h : ∀ k, ‖dg0 D' x k‖ < η) :
    ∃ z : ℂ, z ^ (m + 2) = D' ∧ ∀ k, ‖x k - z‖ ≤ 6 * η * ‖z‖ := by
  have hP0 : (∏ k, x k) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hx k)
  obtain ⟨P, hP⟩ : ∃ P, P = ∏ k, x k := ⟨_, rfl⟩
  rw [← hP] at hP0
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = D' / P := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Fin (m + 1) → ℂ, e = fun k => dg0 D' x k := ⟨_, rfl⟩
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have he1 : ∀ k, (1 - e k) * x k = ρ := by
    intro k
    have := hx k
    simp only [he, dg0, ← hP, ← hρ]
    field_simp
    ring
  have hη8 : η ≤ 1 / 8 := by
    refine hη'.trans ?_
    apply one_div_le_one_div_of_le <;> linarith
  have hen : ∀ k, ‖e k‖ < η := by intro k; rw [he]; exact h k
  have hen2 : ∀ k, ‖-e k‖ ≤ 1 / 2 := by
    intro k; rw [norm_neg]; linarith [hen k]
  have h1e : ∀ k, 7 / 8 ≤ ‖1 - e k‖ := by
    intro k
    have := norm_sub_norm_le (1 : ℂ) (e k)
    rw [norm_one] at this
    linarith [hen k]
  have h1e0 : ∀ k, 1 - e k ≠ 0 := by
    intro k hk
    have := h1e k
    rw [hk, norm_zero] at this
    linarith
  obtain ⟨L, hL⟩ : ∃ L : ℂ, L = (∑ k, Complex.log (1 + -e k)) / ((m : ℂ) + 2) := ⟨_, rfl⟩
  have hm2 : ((m : ℂ) + 2) ≠ 0 := by
    have : ((m : ℂ) + 2) = ((m + 2 : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact Nat.cast_ne_zero.mpr (by omega)
  have hm2n : ‖((m : ℂ) + 2)‖ = (m : ℝ) + 2 := by
    have : ((m : ℂ) + 2) = (((m : ℝ) + 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hLn : ‖L‖ ≤ 3 / 2 * η := by
    rw [hL, norm_div, hm2n, div_le_iff₀ (by linarith)]
    calc ‖∑ k, Complex.log (1 + -e k)‖ ≤ ∑ k : Fin (m + 1), ‖Complex.log (1 + -e k)‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin (m + 1), 3 / 2 * η := by
          apply Finset.sum_le_sum
          intro k _
          have := Complex.norm_log_one_add_half_le_self (hen2 k)
          rw [norm_neg] at this
          linarith [hen k]
      _ = ((m : ℝ) + 1) * (3 / 2 * η) := by simp
      _ ≤ 3 / 2 * η * ((m : ℝ) + 2) := by nlinarith
  have hexp : Complex.exp L ^ (m + 2) = ∏ k, (1 - e k) := by
    rw [← Complex.exp_nat_mul]
    have : ((m + 2 : ℕ) : ℂ) * L = ∑ k, Complex.log (1 + -e k) := by
      rw [hL]; push_cast; field_simp
    rw [this, Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro k _
    rw [Complex.exp_log]
    · ring
    · rw [← sub_eq_add_neg]; exact h1e0 k
  have hE0 : (∏ k, (1 - e k)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => h1e0 k)
  have hρpow : ρ ^ (m + 1) = (∏ k, (1 - e k)) * P := by
    rw [hP, ← Finset.prod_mul_distrib]
    simp_rw [he1]
    simp
  have hρP : ρ * P = D' := by rw [hρ]; field_simp
  refine ⟨ρ * Complex.exp (-L), ?_, ?_⟩
  · rw [mul_pow, Complex.exp_neg, inv_pow, hexp, pow_succ, hρpow, ← hρP]
    field_simp
  · intro k
    have hzL : ρ * Complex.exp (-L) * Complex.exp L = ρ := by
      rw [mul_assoc, ← Complex.exp_add]; simp
    have key : (x k - ρ * Complex.exp (-L)) * (1 - e k) =
        ρ * Complex.exp (-L) * (Complex.exp L - 1 + e k) := by
      have h1 := he1 k
      linear_combination h1 - hzL
    have hnum : ‖Complex.exp L - 1 + e k‖ ≤ 4 * η := by
      have h1 : ‖Complex.exp L - 1‖ ≤ 2 * ‖L‖ := Complex.norm_exp_sub_one_le (by linarith)
      have h2 := norm_add_le (Complex.exp L - 1) (e k)
      linarith [hen k]
    have hk := congrArg norm key
    rw [norm_mul, norm_mul] at hk
    have hz0 : 0 ≤ ‖ρ * Complex.exp (-L)‖ := norm_nonneg _
    have hx0 : 0 ≤ ‖x k - ρ * Complex.exp (-L)‖ := norm_nonneg _
    have h3 : ‖x k - ρ * Complex.exp (-L)‖ * (7 / 8) ≤ ‖ρ * Complex.exp (-L)‖ * (4 * η) :=
      calc ‖x k - ρ * Complex.exp (-L)‖ * (7 / 8)
          ≤ ‖x k - ρ * Complex.exp (-L)‖ * ‖1 - e k‖ := mul_le_mul_of_nonneg_left (h1e k) hx0
        _ = ‖ρ * Complex.exp (-L)‖ * ‖Complex.exp L - 1 + e k‖ := hk
        _ ≤ ‖ρ * Complex.exp (-L)‖ * (4 * η) := mul_le_mul_of_nonneg_left hnum hz0
    have h4 : 0 ≤ ‖ρ * Complex.exp (-L)‖ * η := mul_nonneg hz0 hη.le
    nlinarith
end Formalism.FourierDecayAlt.P.G1
