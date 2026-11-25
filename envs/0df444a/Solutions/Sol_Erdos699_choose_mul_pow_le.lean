-- Prove2me | solution 1 for Erdos699.choose_mul_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:53:20.919356+00:00
-- url     : https://prove2.me/submissions/288ba868-01e8-4610-a26b-9675f7dc3690

module
public import Mathlib
public import Definitions.Def_Erdos699_Basic
public import Theorems.Thm_Erdos699_descFactorial_mul_pow_le

set_option autoImplicit false
@[expose] public section
public section
open Erdos699
namespace Erdos699
theorem _root_.solution {i j n : ℕ} (hjn : j ≤ n) :
    j.choose i * n ^ i ≤ n.choose i * j ^ i := by
  have h := descFactorial_mul_pow_le hjn i
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.mul_assoc, Nat.mul_assoc] at h
  exact Nat.le_of_mul_le_mul_left h (Nat.factorial_pos i)
end Erdos699
