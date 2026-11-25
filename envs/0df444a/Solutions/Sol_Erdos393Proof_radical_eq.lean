-- Prove2me | solution 1 for Erdos393Proof.radical_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:22:17.931828+00:00
-- url     : https://prove2.me/submissions/e280f0fa-658e-4cbd-af65-628ab8ecf7fb

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
theorem _root_.solution (n : ℕ) : radical n = ∏ p ∈ n.primeFactors, p := rfl
end Erdos393Proof
