-- Prove2me | solution 1 for Erdos393Proof.radical_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:22:21.687367+00:00
-- url     : https://prove2.me/submissions/a23966b7-f1c2-41ce-843c-bbd8ef96e1e7

module
public import Mathlib
public import Definitions.Def_Erdos393Palomar_Solution

set_option autoImplicit true
@[expose] public section
public section
open Filter Asymptotics
open scoped Nat
open Erdos393Proof
open ABC Polynomial
namespace Erdos393Proof
theorem _root_.solution (n : ℕ) : 0 < radical n :=
  Finset.prod_pos fun _ hp ↦ (Nat.prime_of_mem_primeFactors hp).pos
end Erdos393Proof
