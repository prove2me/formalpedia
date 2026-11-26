-- Prove2me | solution 1 for Erdos287.power_of_two_slopes_have_opposite_parity_multiples
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T09:21:00.533619+00:00
-- url     : https://prove2.me/submissions/940400dc-e52f-4795-9428-cf6219ad4928

import Mathlib

set_option autoImplicit false

/-- Two of the affine forms with power-of-two slopes can be brought to
nearby positions of opposite parity at a common scale. -/
theorem solution (N L i j t : ℕ) (hL : N ≤ L) (hij : i < j) (hj : j < N) :
    ∃ a b : ℕ,
      a % 2 = 0 ∧ b % 2 = 1 ∧
      0 < b ∧ b < a ∧ a ≤ 2 ^ L + 2 ^ N ∧
      a * (2 ^ i * t + 1) = (2 ^ L + 2 ^ j) * t + a ∧
      b * (2 ^ j * t + 1) = (2 ^ L + 2 ^ j) * t + b := by
  let b : ℕ := 2 ^ (L - j) + 1
  let a := b * 2 ^ (j - i)
  have hb₀ : 0 < b := by dsimp [b]; positivity
  have hp₂ (r : ℕ) (hr : 0 < r) : 2 ∣ (2 : ℕ) ^ r := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    exact ⟨2 ^ s, by rw [pow_succ, mul_comm]⟩
  have hmoda : a % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd ((hp₂ (j - i) (by omega)).mul_left b)
  have hmodb : b % 2 = 1 := by
    have h := Nat.mod_eq_zero_of_dvd (hp₂ (L - j) (by omega))
    dsimp [b]
    rw [Nat.add_mod, h]
  have hba : b < a := by
    have ht : (2 : ℕ) ^ 1 ≤ 2 ^ (j - i) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hh := Nat.mul_le_mul_left b ht
    norm_num at hh
    dsimp [a]
    omega
  have hcoefb : b * 2 ^ j = (2 : ℕ) ^ L + 2 ^ j := by
    dsimp [b]
    rw [add_mul, one_mul, ← pow_add, Nat.sub_add_cancel (by omega)]
  have hcoefa : a * 2 ^ i = (2 : ℕ) ^ L + 2 ^ j := by
    dsimp [a]
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hij.le, hcoefb]
  have ha : a ≤ (2 : ℕ) ^ L + 2 ^ N := calc
    a ≤ a * 2 ^ i := Nat.le_mul_of_pos_right _ (by positivity)
    _ = 2 ^ L + 2 ^ j := hcoefa
    _ ≤ 2 ^ L + 2 ^ N := Nat.add_le_add_left (Nat.pow_le_pow_right (by norm_num) hj.le) _
  refine ⟨a, b, hmoda, hmodb, hb₀, hba, ha, ?_, ?_⟩
  · rw [mul_add, ← mul_assoc, hcoefa, mul_one]
  · rw [mul_add, ← mul_assoc, hcoefb, mul_one]

