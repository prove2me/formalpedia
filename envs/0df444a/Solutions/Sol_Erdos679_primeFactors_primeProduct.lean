-- Prove2me | solution 1 for Erdos679.primeFactors_primeProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:21:25.484891+00:00
-- url     : https://prove2.me/submissions/102fd476-b2ae-40e6-b465-345a8fecec08

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
theorem _root_.solution (m : ℕ) :
    (primeProduct m).primeFactors =
      (Finset.range m).image (fun i => Nat.nth Nat.Prime i) := by
  induction m with
  | zero => simp [primeProduct]
  | succ m ih =>
    rw [primeProduct_succ, Nat.primeFactors_mul (primeProduct_pos m).ne'
      (Nat.prime_nth_prime m).ne_zero, ih, (Nat.prime_nth_prime m).primeFactors]
    simp [Finset.range_add_one, Finset.image_insert, Finset.union_singleton]
end Erdos679
