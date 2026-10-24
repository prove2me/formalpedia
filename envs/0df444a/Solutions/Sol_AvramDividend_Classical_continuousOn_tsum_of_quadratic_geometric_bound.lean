-- Prove2me | solution 1 for AvramDividend.Classical.continuousOn_tsum_of_quadratic_geometric_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:07:20.072495+00:00
-- url     : https://prove2.me/submissions/01355aad-f949-487b-874e-cc0e6c8f76d7

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_continuousOn_tsum_of_quadratic_exp_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set

/-- A geometric majorant gives continuity of a quadratic-weighted series. -/
theorem solution
    (f : ℕ → ℝ → ℝ) (K : Set ℝ) (C ρ : ℝ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hf : ∀ n : ℕ, ContinuousOn (f n) K)
    (hbound : ∀ n : ℕ, ∀ x ∈ K,
      ‖f n x‖ ≤ C * ((n : ℝ) ^ 2 * ρ ^ n)) :
    ContinuousOn (fun x : ℝ => ∑' n : ℕ, f n x) K := by
  let r : ℝ := -Real.log ρ
  have hr : 0 < r := by
    change 0 < -Real.log ρ
    exact neg_pos.mpr (Real.log_neg hρ0 hρ1)
  apply continuousOn_tsum_of_quadratic_exp_bound f K C r hr hf
  intro n x hx
  have heq : Real.exp (-r * (n : ℝ)) = ρ ^ n := by
    have he : -r * (n : ℝ) = (n : ℝ) * Real.log ρ := by
      dsimp [r]
      ring
    rw [he, Real.exp_nat_mul, Real.exp_log hρ0]
  simpa only [heq] using hbound n x hx
