-- Prove2me | solution 1 for Erdos679.primeProduct_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:11:04.8958+00:00
-- url     : https://prove2.me/submissions/865c70f4-9e40-4197-a99b-b10ab677cbc9

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

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679
namespace Erdos679
theorem _root_.solution (m : ℕ) : 0 < primeProduct m := by
  exact Finset.prod_pos fun i _ => (Nat.prime_nth_prime i).pos
end Erdos679
