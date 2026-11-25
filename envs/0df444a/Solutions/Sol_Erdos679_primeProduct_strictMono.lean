-- Prove2me | solution 1 for Erdos679.primeProduct_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:30:00.435876+00:00
-- url     : https://prove2.me/submissions/5efbe052-b9e5-46ea-85e5-b4badb54d9c9

module
public import Definitions.Def_Erdos679_StirlingBound
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos679_Analytic
public import Theorems.Thm_Erdos679_primeProduct_pos
public import Theorems.Thm_Erdos679_primeProduct_succ

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679
namespace Erdos679
theorem _root_.solution : StrictMono primeProduct := by
  apply strictMono_nat_of_lt_succ
  intro m
  rw [primeProduct_succ]
  exact lt_mul_of_one_lt_right (primeProduct_pos m) (Nat.prime_nth_prime m).one_lt
end Erdos679
