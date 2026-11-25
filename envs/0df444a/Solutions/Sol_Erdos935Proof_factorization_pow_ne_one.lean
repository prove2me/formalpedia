-- Prove2me | solution 1 for Erdos935Proof.factorization_pow_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:39:01.759119+00:00
-- url     : https://prove2.me/submissions/89dea9b6-e321-4828-a6d6-4db316f44c6c

module
public import Mathlib
public import Definitions.Def_Erdos935Palomar_Solution

set_option autoImplicit true
@[expose] public section
public section
open Filter
open Erdos935Proof
namespace Erdos935Proof
theorem _root_.solution (a : ℕ) {k : ℕ} (hk : 2 ≤ k) (p : ℕ) :
    (a ^ k).factorization p ≠ 1 := by
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  intro h
  have := Nat.eq_one_of_mul_eq_one_right h
  omega
end Erdos935Proof
