-- Prove2me | solution 1 for Erdos393Proof.radical_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:33:09.658673+00:00
-- url     : https://prove2.me/submissions/724ca71e-a2df-408e-9c32-7f9e3408a035

module
public import Mathlib
public import Definitions.Def_Erdos393Palomar_Solution
public import Theorems.Thm_Erdos393Proof_radical_eq

set_option autoImplicit true
@[expose] public section
public section
open Filter Asymptotics
open scoped Nat
open Erdos393Proof
open ABC Polynomial
namespace Erdos393Proof
theorem _root_.solution (n : ℕ) {k : ℕ} (hk : k ≠ 0) : radical (n ^ k) = radical n := by
  rw [radical_eq, radical_eq, Nat.primeFactors_pow n hk]
end Erdos393Proof
