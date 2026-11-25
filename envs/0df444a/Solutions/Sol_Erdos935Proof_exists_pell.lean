-- Prove2me | solution 1 for Erdos935Proof.exists_pell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:38:49.059246+00:00
-- url     : https://prove2.me/submissions/c9964b15-5d67-4bc4-8939-98c2be54cbe7

module
public import Mathlib
public import Definitions.Def_Erdos935Palomar_Solution

set_option autoImplicit true
@[expose] public section
public section
open Filter
open Erdos935Proof
namespace Erdos935Proof
theorem _root_.solution (k : ℕ) :
    ∃ x y : ℕ, x ^ 2 = 8 * y ^ 2 + 1 ∧ 3 ^ (k + 1) ∣ x ∧ k < y := by
  induction k with
  | zero => exact ⟨3, 1, by norm_num, by norm_num, by norm_num⟩
  | succ k ih =>
    obtain ⟨x, y, h, hx, hy⟩ := ih
    refine ⟨x * (x ^ 2 + 24 * y ^ 2), y * (3 * x ^ 2 + 8 * y ^ 2), ?_, ?_, ?_⟩
    · have hz : (x : ℤ) ^ 2 = 8 * (y : ℤ) ^ 2 + 1 := by exact_mod_cast h
      -- the norm of $(x + y\sqrt 8)^3$ is the cube of the norm of $x + y\sqrt 8$
      have : ((x : ℤ) * (x ^ 2 + 24 * y ^ 2)) ^ 2 =
          8 * ((y : ℤ) * (3 * x ^ 2 + 8 * y ^ 2)) ^ 2 + 1 := by
        linear_combination (((x : ℤ) ^ 2 - 8 * y ^ 2) ^ 2 + ((x : ℤ) ^ 2 - 8 * y ^ 2) + 1) * hz
      exact_mod_cast this
    · have h3 : 3 ∣ x := (dvd_pow_self 3 k.succ_ne_zero).trans hx
      rw [pow_succ]
      exact mul_dvd_mul hx
        (Nat.dvd_add (dvd_pow h3 two_ne_zero) (Dvd.dvd.mul_right (by norm_num) _))
    · have hy2 : 1 ≤ y ^ 2 := Nat.one_le_pow _ _ (by omega)
      have h8 : 8 ≤ 3 * x ^ 2 + 8 * y ^ 2 := by omega
      exact (by omega : k + 1 < y * 8).trans_le (Nat.mul_le_mul_left y h8)
end Erdos935Proof
