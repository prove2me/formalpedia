-- Prove2me | solution 1 for CircStability.Main.fNum_max_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:43:03.28582+00:00
-- url     : https://prove2.me/submissions/1f4c6e1a-e996-4844-a22c-bb559fe42713

import Mathlib
import Definitions.Def_CircStability_Main_Setting
open Finset SimpleGraph

open CircStability.Main in
theorem solution (n c a b k : ℕ) (hcn : c ≤ n) (hbc : b ≤ c)
    (hak : a ≤ k) (hkb : k ≤ b) :
    fNum n k c ≤ max (fNum n a c) (fNum n b c) := by
  have hcast : ∀ x, x ≤ c → (fNum n x c : ℝ) =
      ((c:ℝ) - x + 1) * ((c:ℝ) - x) / 2 + x * ((n:ℝ) - c + x - 1) := by
    intro x hx
    unfold fNum
    have e1 : ((c - x + 1 : ℕ) : ℝ) = (c:ℝ) - x + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hx, Nat.cast_one]
    have e3 : ((x : ℕ) : ℝ) * ((n - c + x - 1 : ℕ) : ℝ) = x * ((n:ℝ) - c + x - 1) := by
      rcases Nat.eq_zero_or_pos x with h0 | hpos
      · subst h0; simp
      · have e2 : ((n - c + x - 1 : ℕ) : ℝ) = (n:ℝ) - c + x - 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_sub hcn, Nat.cast_one]
        rw [e2]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_choose_two, e1, e3]
    ring
  have key : (fNum n k c : ℝ) ≤ max (fNum n a c : ℝ) (fNum n b c : ℝ) := by
    rw [hcast k (by omega), hcast a (by omega), hcast b (by omega)]
    set g : ℝ → ℝ := fun x => ((c:ℝ) - x + 1) * ((c:ℝ) - x) / 2 + x * ((n:ℝ) - c + x - 1) with hg
    show g k ≤ max (g a) (g b)
    rcases Nat.eq_or_lt_of_le (le_trans hak hkb) with hab | hab
    · have : k = a := by omega
      rw [this]; exact le_max_left _ _
    · have hab' : (a:ℝ) < b := by exact_mod_cast hab
      have hak' : (a:ℝ) ≤ k := by exact_mod_cast hak
      have hkb' : (k:ℝ) ≤ b := by exact_mod_cast hkb
      have hid : ((b:ℝ) - k) * g a + ((k:ℝ) - a) * g b - ((b:ℝ) - a) * g k =
          3 / 2 * ((b:ℝ) - a) * ((k:ℝ) - a) * ((b:ℝ) - k) := by
        simp only [hg]; ring
      have hnn : 0 ≤ 3 / 2 * ((b:ℝ) - a) * ((k:ℝ) - a) * ((b:ℝ) - k) := by
        apply mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith))
        linarith
      set M := max (g a) (g b)
      have h1 : ((b:ℝ) - k) * g a ≤ ((b:ℝ) - k) * M :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
      have h2 : ((k:ℝ) - a) * g b ≤ ((k:ℝ) - a) * M :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
      have h3 : ((b:ℝ) - a) * g k ≤ ((b:ℝ) - a) * M := by nlinarith
      exact le_of_mul_le_mul_left h3 (by linarith)
  exact_mod_cast key
