-- Prove2me | solution 1 for Erdos699.descFactorial_mul_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:48:28.036702+00:00
-- url     : https://prove2.me/submissions/c1f8fd26-1988-4d7b-835c-4c55817d64f4

module
public import Mathlib
public import Definitions.Def_Erdos699_Basic

set_option autoImplicit false
@[expose] public section
public section
open Erdos699
namespace Erdos699
theorem _root_.solution {j n : ℕ} (hjn : j ≤ n) :
    ∀ i : ℕ, j.descFactorial i * n ^ i ≤ n.descFactorial i * j ^ i
  | 0 => by simp
  | i + 1 => by
    have ih := solution hjn i
    have key : (j - i) * n ≤ (n - i) * j := by
      rw [Nat.sub_mul, Nat.sub_mul, Nat.mul_comm n j]
      exact Nat.sub_le_sub_left (Nat.mul_le_mul_left i hjn) _
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
    calc (j - i) * j.descFactorial i * (n ^ i * n)
        = ((j - i) * n) * (j.descFactorial i * n ^ i) := by ring
      _ ≤ ((n - i) * j) * (n.descFactorial i * j ^ i) := Nat.mul_le_mul key ih
      _ = (n - i) * n.descFactorial i * (j ^ i * j) := by ring
end Erdos699
