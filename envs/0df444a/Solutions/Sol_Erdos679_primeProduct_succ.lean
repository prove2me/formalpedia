-- Prove2me | solution 1 for Erdos679.primeProduct_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:10:52.702729+00:00
-- url     : https://prove2.me/submissions/1e178e4c-089f-4ae3-9bcc-6cfe76c43eca

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
    primeProduct (m + 1) = primeProduct m * Nat.nth Nat.Prime m :=
  Finset.prod_range_succ _ _
end Erdos679
