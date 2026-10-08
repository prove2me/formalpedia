-- Prove2me | solution 1 for EulerMascheroni.Sondow.scaled_integral_bounds_eventually
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-04T14:19:36.215984+00:00
-- url     : https://prove2.me/submissions/3abae570-12ac-4229-a499-b16c08ab1c8b

import Theorems.Thm_EulerMascheroni_Sondow_integral_bounds
import Theorems.Thm_EulerMascheroni_Sondow_d_le_pow_eventually
import Mathlib.Tactic

open EulerMascheroni.Sondow

theorem solution :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
      0 < (d (2*n) : ℝ) * I n ∧ (d (2*n) : ℝ) * I n < (1/2 : ℝ)^n := by
  have hb : Real.exp 1 < (2.8 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (d_le_pow_eventually 2.8 hb)
  refine ⟨N, fun n hn hpos => ?_⟩
  obtain ⟨hI0, hI1⟩ := integral_bounds n hpos
  have hd0 : (0 : ℝ) < d (2*n) := by
    have hne : d (2*n) ≠ 0 := by
      unfold d
      rw [Ne, Finset.lcm_eq_zero_iff]
      simp
    exact_mod_cast Nat.pos_of_ne_zero hne
  have hdle : (d (2*n) : ℝ) ≤ (2.8 : ℝ) ^ (2*n) := hN (2*n) (by omega)
  refine ⟨mul_pos hd0 hI0, ?_⟩
  calc (d (2*n) : ℝ) * I n ≤ (2.8 : ℝ) ^ (2*n) * I n :=
        mul_le_mul_of_nonneg_right hdle hI0.le
    _ < (2.8 : ℝ) ^ (2*n) * (1/16 : ℝ) ^ n :=
        mul_lt_mul_of_pos_left hI1 (by positivity)
    _ = ((2.8 : ℝ) ^ 2 / 16) ^ n := by
        rw [pow_mul, div_eq_mul_one_div ((2.8:ℝ)^2) 16, mul_pow]
    _ ≤ (1/2 : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
