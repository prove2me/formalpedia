-- Prove2me | solution 1 for ConvexOptAlg.FrankWolfe.thm_3_8_induction
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-06T13:44:32.519235+00:00
-- url     : https://prove2.me/submissions/64baf888-2019-4b52-aa07-54b18c266b6c

import Mathlib

set_option maxHeartbeats 800000

theorem solution (δ : ℕ → ℝ) (β R : ℝ) (hβ : 0 ≤ β)
    (h2 : δ 2 ≤ β / 2 * R ^ 2)
    (hrec : ∀ s : ℕ, 2 ≤ s →
      δ (s + 1) ≤ (1 - 2 / ((s : ℝ) + 1)) * δ s + β / 2 * (2 / ((s : ℝ) + 1)) ^ 2 * R ^ 2)
    (t : ℕ) (ht : 2 ≤ t) :
    δ t ≤ 2 * β * R ^ 2 / ((t : ℝ) + 1) := by
  have hC : 0 ≤ β * R ^ 2 := mul_nonneg hβ (sq_nonneg R)
  induction t, ht using Nat.le_induction with
  | base =>
      norm_num
      nlinarith
  | succ s hs ih =>
      have hs' : (2 : ℝ) ≤ s := by exact_mod_cast hs
      have ha : 0 < (s : ℝ) + 1 := by positivity
      have hb : 0 < (s : ℝ) + 2 := by positivity
      have hg : 0 ≤ 1 - 2 / ((s : ℝ) + 1) := by
        rw [sub_nonneg, div_le_one ha]
        linarith
      calc
        δ (s + 1) ≤ (1 - 2 / ((s : ℝ) + 1)) * δ s +
            β / 2 * (2 / ((s : ℝ) + 1)) ^ 2 * R ^ 2 := hrec s hs
        _ ≤ (1 - 2 / ((s : ℝ) + 1)) * (2 * β * R ^ 2 / ((s : ℝ) + 1)) +
            β / 2 * (2 / ((s : ℝ) + 1)) ^ 2 * R ^ 2 := by
          exact add_le_add (mul_le_mul_of_nonneg_left ih hg) le_rfl
        _ = 2 * (β * R ^ 2) * (s : ℝ) / ((s : ℝ) + 1) ^ 2 := by
          field_simp
          ring
        _ ≤ 2 * β * R ^ 2 / ((s + 1 : ℕ) + 1 : ℝ) := by
          rw [Nat.cast_add, Nat.cast_one]
          apply (div_le_div_iff₀ (sq_pos_of_pos ha) (by positivity)).mpr
          nlinarith
