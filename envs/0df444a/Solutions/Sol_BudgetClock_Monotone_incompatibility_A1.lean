-- Prove2me | solution 1 for BudgetClock.Monotone.incompatibility_A1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:07:47.287374+00:00
-- url     : https://prove2.me/submissions/6ce43a7f-1cf6-4c25-bbc1-83a18e1a78f6

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_BudgetClock_Monotone_Mechanism
set_option autoImplicit false

theorem solution (t : ℕ) (ht : 3 ≤ t) (ρ α β u x : ℝ) (hρ : 19 / 4 ≤ ρ)
    (hα : (2 : ℝ) ^ (t - 2) / ((2 : ℝ) ^ (t - 1) + 2) ≤ α)
    (hβ : β ≤ 3 / 2 - 1 / (2 : ℝ) ^ (t - 2)) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ¬ (ρ * α - β < x ∧ ρ * (1 - u) - β < x ∧
        x < (2 * ρ * α + 2 * β - ρ * u + ρ / (2 : ℝ) ^ (t - 2)) / (2 * ρ - 2)) := by
  rintro ⟨h1, h2, h3⟩
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 3 := ⟨t - 3, by omega⟩
  have e1 : k + 3 - 2 = k + 1 := by omega
  have e2 : k + 3 - 1 = k + 2 := by omega
  rw [e1, e2] at hα
  rw [e1] at hβ h3
  set w : ℝ := (2 : ℝ) ^ (k + 1) with hw
  have hw2 : 2 ≤ w := by
    have : (2:ℝ) ^ 1 ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    simpa using this
  have hw0 : 0 < w := by linarith
  have e3 : (2 : ℝ) ^ (k + 2) = 2 * w := by rw [hw]; ring
  rw [e3] at hα
  set v : ℝ := 1 / w with hv
  have hv0 : 0 < v := by positivity
  have hv1 : v ≤ 1 / 2 := by
    rw [hv, div_le_div_iff₀ hw0 (by norm_num)]; linarith
  have hwv : w * v = 1 := by rw [hv]; field_simp
  have hρ0 : 0 < ρ := by linarith
  have hρ1 : 0 < 2 * ρ - 2 := by linarith
  have hα' : 1 ≤ α * (2 + 2 * v) := by
    rw [div_le_iff₀ (by linarith)] at hα
    -- w ≤ α (2w+2); multiply by v
    have : w * v ≤ α * (2 * w + 2) * v := mul_le_mul_of_nonneg_right hα hv0.le
    nlinarith
  have hα0 : 0 < α := by
    by_contra h
    push_neg at h
    nlinarith
  have hr : ρ / w = ρ * v := by rw [hv]; ring
  rw [hr] at h3
  rw [lt_div_iff₀ hρ1] at h3
  have hA : ρ * (2 * ρ * α - 4 * α - 2 * β + u - v) < 0 := by nlinarith
  have hB : ρ * (2 * ρ * (1 - u) - 2 + 3 * u - 2 * β - v - 2 * α) < 0 := by nlinarith
  have hA' : 2 * ρ * α - 4 * α - 2 * β + u - v < 0 := by
    by_contra h; push_neg at h; nlinarith
  have hB' : 2 * ρ * (1 - u) - 2 + 3 * u - 2 * β - v - 2 * α < 0 := by
    by_contra h; push_neg at h; nlinarith
  have hp1 : 19 / 4 * α ≤ ρ * α := mul_le_mul_of_nonneg_right hρ hα0.le
  have hp2 : 19 / 4 * (1 - u) ≤ ρ * (1 - u) := mul_le_mul_of_nonneg_right hρ (by linarith)
  nlinarith
