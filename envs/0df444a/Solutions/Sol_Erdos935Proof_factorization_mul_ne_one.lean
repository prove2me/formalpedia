-- Prove2me | solution 1 for Erdos935Proof.factorization_mul_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:38:52.836902+00:00
-- url     : https://prove2.me/submissions/e46d8223-43d7-409f-9049-8f4d69aab7f3

module
public import Mathlib
public import Definitions.Def_Erdos935Palomar_Solution

set_option autoImplicit true
@[expose] public section
public section
open Filter
open Erdos935Proof
namespace Erdos935Proof
theorem _root_.solution {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (ha1 : ∀ p, a.factorization p ≠ 1) (hb1 : ∀ p, b.factorization p ≠ 1) (p : ℕ) :
    (a * b).factorization p ≠ 1 := by
  rw [Nat.factorization_mul ha hb, Finsupp.add_apply]
  have := ha1 p
  have := hb1 p
  omega
end Erdos935Proof
