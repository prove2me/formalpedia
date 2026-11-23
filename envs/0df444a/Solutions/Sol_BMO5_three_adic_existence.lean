-- Prove2me | solution 1 for BMO5.three_adic_existence
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T16:57:50.972629+00:00
-- url     : https://prove2.me/submissions/e4237c63-3c29-47d4-baae-071455ac3f91

import Mathlib

namespace BMO5E

theorem four_pow : ∀ m : ℕ, (3:ℤ) ^ (m + 1) ∣ 4 ^ (3 ^ m) - 1
  | 0 => by norm_num
  | m + 1 => by
    have ih := four_pow m
    have h3 : (3:ℤ) ∣ 4 ^ (3 ^ m) - 1 := dvd_trans (dvd_pow_self 3 (Nat.succ_ne_zero m)) ih
    have e : (4:ℤ) ^ (3 ^ (m + 1)) - 1 =
        (4 ^ (3 ^ m) - 1) * ((4 ^ (3 ^ m) - 1) ^ 2 + 3 * 4 ^ (3 ^ m)) := by
      rw [pow_succ 3 m, pow_mul]; ring
    rw [e, pow_succ (3:ℤ) (m + 1)]
    exact mul_dvd_mul ih (dvd_add (dvd_pow h3 two_ne_zero) (dvd_mul_right 3 _))

theorem exist : ∀ k r : ℕ, r < 2 → ∃ i, i % 2 = r ∧ 3 ^ k ∣ 20 * 2 ^ i + i + 1
  | 0 => fun r hr => ⟨r, Nat.mod_eq_of_lt hr, by simp⟩
  | k + 1 => fun r hr => by
    obtain ⟨i, hi2, u, hu⟩ := exist k r hr
    obtain ⟨q, t, _, rfl⟩ : ∃ q t, t < 3 ∧ u = 3 * q + t :=
      ⟨u / 3, u % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod u 3).symm⟩
    refine ⟨i + 2 * (3 ^ k * t), by rw [Nat.add_mul_mod_self_left]; exact hi2, ?_⟩
    have h4 : (3:ℤ) ^ (k + 1) ∣ 4 ^ (3 ^ k * t) - 1 := by
      rw [pow_mul]
      exact dvd_trans (four_pow k) (by simpa using sub_dvd_pow_sub_pow ((4:ℤ) ^ (3 ^ k)) 1 t)
    have h24 : (2:ℤ) ^ (2 * (3 ^ k * t)) = 4 ^ (3 ^ k * t) := by rw [pow_mul]; norm_num
    have hu' : (20 * 2 ^ i + i + 1 : ℤ) = 3 ^ k * (3 * q + t) := by exact_mod_cast hu
    have hZ : (3:ℤ) ^ (k + 1) ∣ 20 * 2 ^ (i + 2 * (3 ^ k * t)) + ((i:ℤ) + 2 * (3 ^ k * t)) + 1 := by
      have e : (20:ℤ) * 2 ^ (i + 2 * (3 ^ k * t)) + ((i:ℤ) + 2 * (3 ^ k * t)) + 1
          = 20 * 2 ^ i * (4 ^ (3 ^ k * t) - 1) + 3 ^ (k + 1) * (q + t) := by
        rw [pow_add, h24, pow_succ]
        linear_combination hu'
      rw [e]
      exact dvd_add (dvd_mul_of_dvd_right h4 _) (dvd_mul_right _ _)
    exact_mod_cast hZ

end BMO5E

theorem solution (k r : ℕ) (hr : r < 2) :
    ∃ i, i % 2 = r ∧ 3 ^ k ∣ 20 * 2 ^ i + i + 1 := BMO5E.exist k r hr
