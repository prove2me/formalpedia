-- Prove2me | solution 1 for Erdos287.explicit_power_dominates_truncated_denominator
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T14:43:20.700925+00:00
-- url     : https://prove2.me/submissions/b80bda5d-2ef7-467b-a1ca-186baa3b8ac0

import Mathlib

set_option autoImplicit false

/-- An explicit prime-power precision that dominates the least common
multiple of all possible surviving prime powers up to the cutoff. -/
theorem solution (Y p : ℕ) (hp : 2 ≤ p) :
    Nat.lcmUpto Y < p ^ ((10 * Y) / Nat.log 2 p + 1) := by
  have hhalf := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
  rw [Real.log_inv] at hhalf
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by norm_num at hhalf ⊢; linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hweak : (Nat.lcmUpto Y : ℝ) ≤ (2 : ℝ) ^ (10 * Y) := by
    have hY : (0 : ℝ) ≤ (Y : ℝ) := by positivity
    have hlog : Real.log (Nat.lcmUpto Y : ℝ) ≤ Real.log ((2 : ℝ) ^ (10 * Y)) := by
      rw [← Chebyshev.psi_eq_log_lcmUpto, Real.log_pow]
      push_cast
      calc
        _ ≤ (Real.log 4 + 4) * Y := Chebyshev.psi_le_const_mul_self hY
        _ ≤ (10 * (Y : ℝ)) * Real.log 2 := by
          rw [hlog4]
          have h := mul_le_mul_of_nonneg_right (show (2 : ℝ) * Real.log 2 + 4 ≤
            10 * Real.log 2 by linarith) hY
          linarith
    exact (Real.log_le_log_iff (by exact_mod_cast Nat.lcmUpto_pos Y)
      (by positivity)).mp hlog
  let b := Nat.log 2 p
  let j := (10 * Y) / b + 1
  have hb : 0 < b := Nat.log_pos (by decide) hp
  change Nat.lcmUpto Y < p ^ j
  have hj : 10 * Y < b * j := by
    dsimp only [j]
    rw [Nat.mul_add, mul_one]
    have hm := Nat.mod_lt (10 * Y) hb
    have he := Nat.mod_add_div (10 * Y) b
    omega
  calc
    _ ≤ 2 ^ (10 * Y) := by exact_mod_cast hweak
    _ < 2 ^ (b * j) := Nat.pow_lt_pow_right (by decide) hj
    _ = (2 ^ b) ^ j := pow_mul 2 b j
    _ ≤ p ^ j := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (by omega : p ≠ 0)) _

