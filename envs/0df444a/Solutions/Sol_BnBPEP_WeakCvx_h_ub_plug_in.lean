-- Prove2me | solution 1 for BnBPEP.WeakCvx.h_ub_plug_in
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T08:34:01.152011+00:00
-- url     : https://prove2.me/submissions/706bd51e-75c6-45c5-b4bb-a6c19db48140

import Mathlib
set_option autoImplicit false

theorem solution (N : ℕ) (L κ : ℝ) (hL : 0 < L) (hκ : 0 ≤ κ) :
    L ^ 2 / ((N : ℝ) + 1) * (-1
        + 1 / (2 * (√(4 * κ ^ 2 * ((N : ℝ) + 1) + 1) / (2 * ((N : ℝ) + 1))))
          * (1 / ((N : ℝ) + 1) + 4 * κ ^ 2)
        + 2 * (√(4 * κ ^ 2 * ((N : ℝ) + 1) + 1) / (2 * ((N : ℝ) + 1))) * ((N : ℝ) + 1))
      = L ^ 2 * (2 * √(4 * κ ^ 2 * ((N : ℝ) + 1) + 1) - 1) / ((N : ℝ) + 1) ∧
    ∀ h : ℝ, 0 < h →
      L ^ 2 / ((N : ℝ) + 1) * (-1
          + 1 / (2 * (√(4 * κ ^ 2 * ((N : ℝ) + 1) + 1) / (2 * ((N : ℝ) + 1))))
            * (1 / ((N : ℝ) + 1) + 4 * κ ^ 2)
          + 2 * (√(4 * κ ^ 2 * ((N : ℝ) + 1) + 1) / (2 * ((N : ℝ) + 1))) * ((N : ℝ) + 1))
        ≤ L ^ 2 / ((N : ℝ) + 1) * (-1 + 1 / (2 * h) * (1 / ((N : ℝ) + 1) + 4 * κ ^ 2)
          + 2 * h * ((N : ℝ) + 1)) := by
  have hn : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  generalize hnn : (N : ℝ) + 1 = n at hn ⊢
  have hpos : 0 < 4 * κ ^ 2 * n + 1 := by positivity
  have hs0 : 0 < √(4 * κ ^ 2 * n + 1) := Real.sqrt_pos.mpr hpos
  have hs2 : √(4 * κ ^ 2 * n + 1) ^ 2 = 4 * κ ^ 2 * n + 1 := Real.sq_sqrt hpos.le
  generalize √(4 * κ ^ 2 * n + 1) = s at hs0 hs2 ⊢
  have key : -1 + 1 / (2 * (s / (2 * n))) * (1 / n + 4 * κ ^ 2) + 2 * (s / (2 * n)) * n
      = 2 * s - 1 := by
    field_simp
    nlinarith [hs2]
  have hc : 0 < L ^ 2 / n := by positivity
  refine ⟨?_, ?_⟩
  · rw [key]; ring
  · intro h hh
    rw [key]
    apply mul_le_mul_of_nonneg_left _ hc.le
    have h1 : 1 / (2 * h) * (1 / n + 4 * κ ^ 2) = s ^ 2 / (2 * h * n) := by
      field_simp
      nlinarith [hs2]
    rw [h1]
    have : 2 * s ≤ s ^ 2 / (2 * h * n) + 2 * h * n := by
      have hp : 0 < 2 * h * n := by positivity
      rw [← sub_nonneg]
      have : s ^ 2 / (2 * h * n) + 2 * h * n - 2 * s = (s - 2 * h * n) ^ 2 / (2 * h * n) := by
        field_simp
        ring
      rw [this]; positivity
    linarith
