-- Prove2me | solution 1 for FairReplay.eq_45
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-12T14:57:59.206205+00:00
-- url     : https://prove2.me/submissions/0dae8990-1b4b-4860-8f90-7860e406e89c

import Mathlib

set_option autoImplicit false

/-- `K_edge = d + O(d²)`: the Taylor expansion of `r log(r/(r-d))` at `d = 0`, with the explicit
bound `|r log(r/(r-d)) - d| ≤ (2/r) d²` for `d < r/2`. -/
theorem solution (p s : ℝ) (hp : 0 < p) (hs : 0 < s) (hps : p + s < 1) :
    ∃ C d₀ : ℝ, 0 < C ∧ 0 < d₀ ∧ ∀ d : ℝ, 0 < d → d < d₀ →
      |(1 - p - s) * Real.log ((1 - p - s) / ((1 - p - s) - d)) - d| ≤ C * d ^ 2 := by
  have hr : 0 < 1 - p - s := by linarith
  refine ⟨2 / (1 - p - s), (1 - p - s) / 2, by positivity, by positivity, ?_⟩
  intro d hd0 hdlt
  set r : ℝ := 1 - p - s with hrdef
  set t : ℝ := d / r with ht
  have ht0 : 0 < t := div_pos hd0 hr
  have ht1 : t < 1 / 2 := by
    rw [ht, div_lt_iff₀ hr]
    linarith
  have h1t : 0 < 1 - t := by linarith
  have hlogeq : Real.log (r / (r - d)) = -Real.log (1 - t) := by
    have hratio : r / (r - d) = (1 - t)⁻¹ := by
      rw [ht]
      field_simp
    rw [hratio, Real.log_inv]
  have hdeq : r * Real.log (r / (r - d)) - d = r * (-Real.log (1 - t) - t) := by
    rw [hlogeq, ht]
    field_simp
  have hlow : 0 ≤ -Real.log (1 - t) - t := by
    have h := Real.log_le_sub_one_of_pos h1t
    linarith
  have hhigh : -Real.log (1 - t) - t ≤ 2 * t ^ 2 := by
    have hinv : 0 < (1 - t)⁻¹ := inv_pos.mpr h1t
    have h := Real.log_le_sub_one_of_pos hinv
    rw [Real.log_inv] at h
    have hone : (1 - t)⁻¹ - 1 = t / (1 - t) := by
      field_simp
      ring
    have hle : -Real.log (1 - t) ≤ t / (1 - t) := by linarith
    have hsimp : t / (1 - t) - t = t ^ 2 / (1 - t) := by
      field_simp
      ring
    have hbound : t ^ 2 / (1 - t) ≤ 2 * t ^ 2 := by
      rw [div_le_iff₀ h1t]
      nlinarith [ht0, ht1]
    linarith
  have habs : |r * Real.log (r / (r - d)) - d| = r * (-Real.log (1 - t) - t) := by
    rw [hdeq, abs_of_nonneg (mul_nonneg hr.le hlow)]
  rw [habs]
  calc r * (-Real.log (1 - t) - t) ≤ r * (2 * t ^ 2) :=
        mul_le_mul_of_nonneg_left hhigh hr.le
    _ = (2 / r) * d ^ 2 := by
        rw [ht]
        field_simp
