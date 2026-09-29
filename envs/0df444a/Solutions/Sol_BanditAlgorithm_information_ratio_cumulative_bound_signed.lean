-- Prove2me | solution 1 for BanditAlgorithm.information_ratio_cumulative_bound_signed
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T21:35:07.408112+00:00
-- url     : https://prove2.me/submissions/7d14932a-40e1-4e44-803d-81fc861233f7

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

namespace BanditAlgorithm

theorem _root_.solution {n : ℕ}
    (δ info : Fin n → ℝ) (Γ H : ℝ)
    (hΓ : 0 ≤ Γ) (hH : 0 ≤ H)
    (hpoint : ∀ t, δ t ^ 2 ≤ Γ * info t)
    (hsum : ∑ t, info t ≤ H) :
    ∑ t, δ t ≤ Real.sqrt (n * Γ * H) := by
  have hsquares :
      (∑ t, δ t) ^ 2 ≤ (n : ℝ) * ∑ t, δ t ^ 2 := by
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin n ↦ (1 : ℝ)) δ)
  have hpoints :
      ∑ t, δ t ^ 2 ≤ ∑ t, Γ * info t :=
    Finset.sum_le_sum fun t _ ↦ hpoint t
  have hmain : (∑ t, δ t) ^ 2 ≤ n * Γ * H := by
    calc
      (∑ t, δ t) ^ 2
          ≤ (n : ℝ) * ∑ t, δ t ^ 2 := hsquares
      _ ≤ (n : ℝ) * ∑ t, Γ * info t := by gcongr
      _ = (n : ℝ) * Γ * ∑ t, info t := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ (n : ℝ) * Γ * H := by gcongr
  have hrad : 0 ≤ (n : ℝ) * Γ * H :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hΓ) hH
  by_cases hδsum : 0 ≤ ∑ t, δ t
  · nlinarith [Real.sq_sqrt hrad, Real.sqrt_nonneg ((n : ℝ) * Γ * H)]
  · exact (le_of_lt (lt_of_not_ge hδsum)).trans (Real.sqrt_nonneg _)

end BanditAlgorithm
