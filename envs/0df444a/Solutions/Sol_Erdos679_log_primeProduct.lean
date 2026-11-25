-- Prove2me | solution 1 for Erdos679.log_primeProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:20:25.832362+00:00
-- url     : https://prove2.me/submissions/6c8ca8bd-dcf1-4613-ac3c-070277333373

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
theorem _root_.solution (m : ℕ) :
    log (primeProduct m : ℝ) = ∑ i ∈ Finset.range m, log (Nat.nth Nat.Prime i) := by
  rw [primeProduct, Nat.cast_prod, Real.log_prod]
  intro i _
  exact_mod_cast (Nat.prime_nth_prime i).ne_zero
end Erdos679
