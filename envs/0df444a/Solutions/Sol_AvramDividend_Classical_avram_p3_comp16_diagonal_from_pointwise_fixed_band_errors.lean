-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_comp16_diagonal_from_pointwise_fixed_band_errors
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:02:06.107969+00:00
-- url     : https://prove2.me/submissions/b527b8e0-1573-4df1-8965-ea398b300b0c

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp16_diagonal_vanishing_error_of_fixed_band_rates

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
noncomputable section

/-! The per-band convergence thresholds may grow arbitrarily quickly. -/
theorem solution
    (Err : ℕ → ℕ → ℝ)
    (hFix : ∀ k, Tendsto (fun n => Err k n) atTop (nhds 0)) :
    ∃ κ : ℕ → ℕ,
      (∀ n, κ n ≤ n) ∧
      Tendsto κ atTop atTop ∧
      Tendsto (fun n => Err (κ n) n) atTop (nhds 0) := by
  classical
  have hb : ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      |Err k n| ≤ (1 : ℝ) / ((k : ℝ) + 1) := by
    intro k
    have he : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hFix k) _ he
    refine ⟨N, ?_⟩
    intro n hn
    have hlt := hN n hn
    simpa [Real.dist_eq] using (le_of_lt hlt)
  let M : ℕ → ℕ := fun k =>
    if k = 0 then 0 else max k (Classical.choose (hb k))
  have hM0 : M 0 = 0 := by simp [M]
  have hMge : ∀ k, k ≤ M k := by
    intro k
    by_cases hk : k = 0
    · subst k; simp [M]
    · simp [M, hk]
  have hMbnd : ∀ k n, 0 < k → M k ≤ n →
      |Err k n| ≤ |(1 : ℝ) / ((k : ℝ) + 1)| := by
    intro k n hk hkn
    have hNk : Classical.choose (hb k) ≤ n := by
      have heq : max k (Classical.choose (hb k)) ≤ n := by
        simpa [M, (Nat.ne_of_gt hk)] using hkn
      exact (Nat.le_max_right _ _).trans heq
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    rw [abs_of_pos hpos]
    exact Classical.choose_spec (hb k) n hNk
  obtain ⟨κ, hκle, _, hκtop, hκerr⟩ :=
    AvramDividend.Classical.avram_p3_comp16_diagonal_vanishing_error_of_fixed_band_rates
      M hM0 hMge
      (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1))
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      Err hMbnd
  exact ⟨κ, hκle, hκtop, hκerr⟩
