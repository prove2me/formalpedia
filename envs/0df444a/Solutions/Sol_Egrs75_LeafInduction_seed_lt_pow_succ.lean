-- Prove2me | solution 1 for Egrs75.LeafInduction.seed_lt_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:29:54.256666+00:00
-- url     : https://prove2.me/submissions/ba437353-8d61-4008-bd05-b44ac0141f5e

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_LeafInduction

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.LeafInduction
open Nat
open Egrs75
namespace Egrs75.LeafInduction
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (N : ℕ) : N < p ^ (N + 1) := by
  have h2 : (2 : ℕ) ^ (N + 1) ≤ p ^ (N + 1) := Nat.pow_le_pow_left hp _
  have hN : N < 2 ^ (N + 1) :=
    lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
  omega
end Egrs75.LeafInduction
