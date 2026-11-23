-- Prove2me | solution 1 for BMO5.halt_level_mod18
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T17:05:53.168139+00:00
-- url     : https://prove2.me/submissions/8d7fdf1b-4fa3-4502-999f-3f6ae21c84b6

import Mathlib

namespace BMO5M18

theorem lt_pow (x : ℕ) : x < 2 ^ x := by
  induction x with
  | zero => norm_num
  | succ x ih => rw [pow_succ]; omega

theorem pow_mod9 (x : ℕ) :
    (x % 6 = 0 ∧ 2 ^ x % 9 = 1) ∨ (x % 6 = 1 ∧ 2 ^ x % 9 = 2) ∨ (x % 6 = 2 ∧ 2 ^ x % 9 = 4) ∨
    (x % 6 = 3 ∧ 2 ^ x % 9 = 8) ∨ (x % 6 = 4 ∧ 2 ^ x % 9 = 7) ∨ (x % 6 = 5 ∧ 2 ^ x % 9 = 5) := by
  induction x with
  | zero => left; norm_num
  | succ x ih => rw [pow_succ]; omega

end BMO5M18

set_option maxHeartbeats 0

theorem solution (a b : ℕ → ℕ) (a_ini : a 0 = 0) (b_ini : b 0 = 5)
    (a_rec : ∀ n, a (n + 1) = if 10 * 2 ^ (a n) - 1 ≤ b n then a n + 1 else a n)
    (b_rec : ∀ n, b (n + 1) = if 10 * 2 ^ (a n) - 1 ≤ b n then b n - (10 * 2 ^ (a n) - 1)
      else 3 * b n + a n + 5) :
    ∀ n, b n = 10 * 2 ^ (a n) - 2 →
      (a n % 18 = 2 ∨ a n % 18 = 5 ∨ a n % 18 = 6 ∨ a n % 18 = 7 ∨ a n % 18 = 8 ∨
       a n % 18 = 11 ∨ a n % 18 = 12 ∨ a n % 18 = 13) := by
  have inv : ∀ n, 2 * b n + a n + 5 < 3 * (20 * 2 ^ (a n) + a n + 3) := by
    intro n
    induction n with
    | zero => rw [a_ini, b_ini]; norm_num
    | succ n ih =>
      have hP : 1 ≤ 2 ^ (a n) := Nat.one_le_two_pow
      by_cases h : 10 * 2 ^ (a n) - 1 ≤ b n
      · rw [a_rec, b_rec, if_pos h, if_pos h, pow_succ]
        generalize 2 ^ (a n) = P at *
        omega
      · rw [a_rec, b_rec, if_neg h, if_neg h]
        generalize 2 ^ (a n) = P at *
        omega
  have sT : ∀ m, ¬ (10 * 2 ^ (a m) - 1 ≤ b m) →
      a (m + 1) = a m ∧ b (m + 1) = 3 * b m + a m + 5 :=
    fun m h => ⟨by rw [a_rec, if_neg h], by rw [b_rec, if_neg h]⟩
  have sS : ∀ m, 10 * 2 ^ (a m) - 1 ≤ b m →
      a (m + 1) = a m + 1 ∧ b (m + 1) = b m - (10 * 2 ^ (a m) - 1) :=
    fun m h => ⟨by rw [a_rec, if_pos h], by rw [b_rec, if_pos h]⟩
  have pw : ∀ m k, a k = a m + 1 → 2 ^ (a k) = 2 * 2 ^ (a m) :=
    fun m k h => by rw [h, pow_succ]; ring
  have pe : ∀ m k, a k = a m → 2 ^ (a k) = 2 ^ (a m) := fun m k h => by rw [h]
  have P1 : ∀ m, 1 ≤ 2 ^ (a m) := fun m => Nat.one_le_two_pow
  have LT : ∀ m, a m < 2 ^ (a m) := fun m => BMO5M18.lt_pow _
  -- the first four states: (0,5) (0,20) (1,11) (1,39)
  obtain ⟨e1, f1⟩ := sT 0 (by rw [a_ini, b_ini]; norm_num)
  have a1 : a 1 = 0 := by show a (0 + 1) = 0; rw [e1, a_ini]
  have b1 : b 1 = 20 := by show b (0 + 1) = 20; rw [f1, a_ini, b_ini]
  obtain ⟨e2, f2⟩ := sS 1 (by rw [a1, b1]; norm_num)
  have a2 : a 2 = 1 := by show a (1 + 1) = 1; rw [e2, a1]
  have b2 : b 2 = 11 := by show b (1 + 1) = 11; rw [f2, a1, b1]; norm_num
  obtain ⟨e3, f3⟩ := sT 2 (by rw [a2, b2]; norm_num)
  have a3 : a 3 = 1 := by show a (2 + 1) = 1; rw [e3, a2]
  have b3 : b 3 = 39 := by show b (2 + 1) = 39; rw [f3, a2, b2]
  intro n hb
  match n, hb with
  | 0, hb => rw [a_ini, b_ini] at hb; norm_num at hb
  | 1, hb => rw [a1, b1] at hb; norm_num at hb
  | 2, hb => rw [a2, b2] at hb; norm_num at hb
  | 3, hb => rw [a3, b3] at hb; norm_num at hb
  | r + 4, hb =>
    have hb4 : b (r + 1 + 1 + 1 + 1) = 10 * 2 ^ (a (r + 1 + 1 + 1 + 1)) - 2 := hb
    show a (r + 1 + 1 + 1 + 1) % 18 = 2 ∨ a (r + 1 + 1 + 1 + 1) % 18 = 5 ∨
      a (r + 1 + 1 + 1 + 1) % 18 = 6 ∨ a (r + 1 + 1 + 1 + 1) % 18 = 7 ∨
      a (r + 1 + 1 + 1 + 1) % 18 = 8 ∨ a (r + 1 + 1 + 1 + 1) % 18 = 11 ∨
      a (r + 1 + 1 + 1 + 1) % 18 = 12 ∨ a (r + 1 + 1 + 1 + 1) % 18 = 13
    clear hb
    by_cases h3 : 10 * 2 ^ (a (r + 1 + 1 + 1)) - 1 ≤ b (r + 1 + 1 + 1)
    · -- subtraction at step n-1
      obtain ⟨ea3, eb3⟩ := sS _ h3
      have q4 := pw _ _ ea3
      by_cases h2 : 10 * 2 ^ (a (r + 1 + 1)) - 1 ≤ b (r + 1 + 1)
      · -- two subtractions before the halt: impossible
        obtain ⟨ea2, eb2⟩ := sS _ h2
        have q3 := pw _ _ ea2
        have i2 := inv (r + 1 + 1)
        have l2 := LT (r + 1 + 1)
        have p2 := P1 (r + 1 + 1)
        omega
      · obtain ⟨ea2, eb2⟩ := sT _ h2
        have q3 := pe _ _ ea2
        by_cases h1 : 10 * 2 ^ (a (r + 1)) - 1 ≤ b (r + 1)
        · obtain ⟨ea1, eb1⟩ := sS _ h1
          have q2 := pw _ _ ea1
          by_cases h0 : 10 * 2 ^ (a r) - 1 ≤ b r
          · -- S S T S: impossible
            obtain ⟨ea0, eb0⟩ := sS _ h0
            have q1 := pw _ _ ea0
            have i0 := inv r
            have l0 := LT r
            have p0 := P1 r
            omega
          · -- T S T S halt
            obtain ⟨ea0, eb0⟩ := sT _ h0
            have q1 := pe _ _ ea0
            have p0 := P1 r
            rcases BMO5M18.pow_mod9 (a r) with ⟨u, v⟩ | ⟨u, v⟩ | ⟨u, v⟩ | ⟨u, v⟩ | ⟨u, v⟩ | ⟨u, v⟩ <;>
              omega
        · -- T T S halt
          obtain ⟨ea1, eb1⟩ := sT _ h1
          have q2 := pe _ _ ea1
          have p1 := P1 (r + 1)
          rcases BMO5M18.pow_mod9 (a (r + 1)) with ⟨u, v⟩ | ⟨u, v⟩ | ⟨u, v⟩ | ⟨u, v⟩ | ⟨u, v⟩ | ⟨u, v⟩ <;>
            omega
    · -- tripling at step n-1
      obtain ⟨ea3, eb3⟩ := sT _ h3
      have q4 := pe _ _ ea3
      by_cases h2 : 10 * 2 ^ (a (r + 1 + 1)) - 1 ≤ b (r + 1 + 1)
      · obtain ⟨ea2, eb2⟩ := sS _ h2
        have q3 := pw _ _ ea2
        by_cases h1 : 10 * 2 ^ (a (r + 1)) - 1 ≤ b (r + 1)
        · -- S S T halt: impossible
          obtain ⟨ea1, eb1⟩ := sS _ h1
          have q2 := pw _ _ ea1
          have i1 := inv (r + 1)
          have l1 := LT (r + 1)
          have p1 := P1 (r + 1)
          omega
        · -- T S T halt
          obtain ⟨ea1, eb1⟩ := sT _ h1
          have q2 := pe _ _ ea1
          have p1 := P1 (r + 1)
          rcases BMO5M18.pow_mod9 (a (r + 1)) with ⟨u, v⟩ | ⟨u, v⟩ | ⟨u, v⟩ | ⟨u, v⟩ | ⟨u, v⟩ | ⟨u, v⟩ <;>
            omega
      · -- T T halt
        obtain ⟨ea2, eb2⟩ := sT _ h2
        have q3 := pe _ _ ea2
        have p2 := P1 (r + 1 + 1)
        rcases BMO5M18.pow_mod9 (a (r + 1 + 1)) with ⟨u, v⟩ | ⟨u, v⟩ | ⟨u, v⟩ | ⟨u, v⟩ | ⟨u, v⟩ | ⟨u, v⟩ <;>
          omega
