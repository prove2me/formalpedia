-- Prove2me | solution 1 for BMO5.three_adic_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T16:49:49.467993+00:00
-- url     : https://prove2.me/submissions/eaeaba7f-2adf-4d90-99aa-83c978d349ce

import Mathlib

namespace BMO5U

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

theorem core (k j d : ℕ) (hd : 2 * 3 ^ k ∣ d)
    (hi : (3:ℤ) ^ (k + 1) ∣ 20 * 2 ^ (j + d) + ((j:ℤ) + d) + 1)
    (hj : (3:ℤ) ^ (k + 1) ∣ 20 * 2 ^ j + (j:ℤ) + 1) : (3:ℤ) ^ (k + 1) ∣ (d:ℤ) := by
  obtain ⟨t, rfl⟩ := hd
  have h4 : (3:ℤ) ^ (k + 1) ∣ 4 ^ (3 ^ k * t) - 1 := by
    rw [pow_mul]
    exact dvd_trans (four_pow k) (by simpa using sub_dvd_pow_sub_pow ((4:ℤ) ^ (3 ^ k)) 1 t)
  have h24 : (2:ℤ) ^ (2 * 3 ^ k * t) = 4 ^ (3 ^ k * t) := by
    rw [mul_assoc, pow_mul]; norm_num
  have h1 : (3:ℤ) ^ (k + 1) ∣ 20 * 2 ^ j * (4 ^ (3 ^ k * t) - 1) := dvd_mul_of_dvd_right h4 _
  have h := dvd_sub (dvd_sub hi hj) h1
  have e : ((2 * 3 ^ k * t : ℕ) : ℤ) =
      20 * 2 ^ (j + 2 * 3 ^ k * t) + ((j:ℤ) + ((2 * 3 ^ k * t : ℕ) : ℤ)) + 1
        - (20 * 2 ^ j + (j:ℤ) + 1) - 20 * 2 ^ j * (4 ^ (3 ^ k * t) - 1) := by
    rw [pow_add, h24]
    push_cast
    ring
  rw [e]
  exact h

theorem uniqd : ∀ k j d : ℕ, d % 2 = 0 → 3 ^ k ∣ 20 * 2 ^ (j + d) + (j + d) + 1 →
    3 ^ k ∣ 20 * 2 ^ j + j + 1 → 3 ^ k ∣ d
  | 0 => by intros; simp
  | k + 1 => by
    intro j d hd hi hj
    have hk : 3 ^ k ∣ d := uniqd k j d hd (dvd_trans (pow_dvd_pow 3 (Nat.le_succ k)) hi)
      (dvd_trans (pow_dvd_pow 3 (Nat.le_succ k)) hj)
    have h2 : 2 ∣ d := Nat.dvd_of_mod_eq_zero hd
    have hc : Nat.Coprime 2 (3 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    have h23 : 2 * 3 ^ k ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd hc h2 hk
    have hi' : (3:ℤ) ^ (k + 1) ∣ 20 * 2 ^ (j + d) + ((j:ℤ) + d) + 1 := by exact_mod_cast hi
    have hj' : (3:ℤ) ^ (k + 1) ∣ 20 * 2 ^ j + (j:ℤ) + 1 := by exact_mod_cast hj
    have := core k j d h23 hi' hj'
    exact_mod_cast this

end BMO5U

theorem solution (k i j : ℕ) (hpar : i % 2 = j % 2)
    (hi : 3 ^ k ∣ 20 * 2 ^ i + i + 1) (hj : 3 ^ k ∣ 20 * 2 ^ j + j + 1) :
    i % 3 ^ k = j % 3 ^ k := by
  rcases le_total j i with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have hd := BMO5U.uniqd k j d (by omega) hi hj
    exact ((Nat.modEq_iff_dvd' (Nat.le_add_right j d)).mpr (by simpa using hd)).symm
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have hd := BMO5U.uniqd k i d (by omega) hj hi
    exact (Nat.modEq_iff_dvd' (Nat.le_add_right i d)).mpr (by simpa using hd)
