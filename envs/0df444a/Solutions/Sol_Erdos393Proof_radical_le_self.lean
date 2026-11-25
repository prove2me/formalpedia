-- Prove2me | solution 1 for Erdos393Proof.radical_le_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:23:03.604549+00:00
-- url     : https://prove2.me/submissions/d9faafa3-9618-41f3-807a-b81552d97f8d

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
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) : radical n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)
end Erdos393Proof
