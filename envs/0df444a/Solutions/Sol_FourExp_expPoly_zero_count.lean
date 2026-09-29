-- Prove2me | solution 1 for FourExp.expPoly_zero_count
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-15T03:45:47.895981+00:00
-- url     : https://prove2.me/submissions/236257b1-311d-4932-b254-754b2381a88d

import Mathlib
import Theorems.Thm_FourExp_expPoly_zero_count_scaled
import Theorems.Thm_FourExp_zero_count_degenerate
import Theorems.Thm_FourExp_zero_count_arith
import Theorems.Thm_FourExp_zero_count_arith_poly

open Finset

theorem solution
    {l : ℕ} (q : Fin l → ℕ) (ω : Fin l → ℂ) (hω : Function.Injective ω)
    (b : (j : Fin l) → Fin (q j) → ℂ) (hb : ∃ j i, b j i ≠ 0)
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) (lam : ℝ) (hlam : 0 < lam)
    (S : Finset ℂ) (hS : ∀ z ∈ S, ‖z - z₀‖ ≤ ρ) :
    (∑ z ∈ S, (analyticOrderNatAt
        (fun w : ℂ => ∑ j, ∑ i : Fin (q j), b j i * w ^ (i : ℕ) * Complex.exp (ω j * w)) z : ℝ))
      < ((∑ j, q j : ℕ) : ℝ) / lam
        + 2 * (1 + ((∑ j, q j : ℕ) : ℝ) ^ lam) / (lam * Real.log ((∑ j, q j : ℕ) : ℝ))
          * (1 + ρ * ⨆ j, ‖ω j‖) := by
  classical
  have hΩ0 : 0 ≤ ⨆ j, ‖ω j‖ := Real.iSup_nonneg (fun j => norm_nonneg _)
  have hx : 0 ≤ ρ * ⨆ j, ‖ω j‖ := mul_nonneg hρ hΩ0
  have hcast : (∑ z ∈ S, (analyticOrderNatAt
      (fun w : ℂ => ∑ j, ∑ i : Fin (q j), b j i * w ^ (i : ℕ) * Complex.exp (ω j * w)) z : ℝ))
      = ((∑ z ∈ S, analyticOrderNatAt
      (fun w : ℂ => ∑ j, ∑ i : Fin (q j), b j i * w ^ (i : ℕ) * Complex.exp (ω j * w)) z : ℕ) : ℝ) := by
    push_cast; rfl
  by_cases hdeg : (∑ j, q j) ≤ 1 ∨ (⨆ j, ‖ω j‖) = 0
  · have h1 := FourExp.zero_count_degenerate q ω hω b hb S hdeg
    rw [hcast]
    exact FourExp.zero_count_arith_poly (∑ j, q j) (ρ * ⨆ j, ‖ω j‖) lam hx hlam _ h1
  · push_neg at hdeg
    obtain ⟨hn, hΩ⟩ := hdeg
    have hΩpos : 0 < ⨆ j, ‖ω j‖ := lt_of_le_of_ne hΩ0 (Ne.symm hΩ)
    have h2 := FourExp.expPoly_zero_count_scaled q ω hω b hb z₀ ρ hρ S hS hΩpos
    exact FourExp.zero_count_arith (∑ j, q j) (by omega) (ρ * ⨆ j, ‖ω j‖) lam hx hlam _
      (Finset.sum_nonneg (fun z _ => Nat.cast_nonneg _)) h2
