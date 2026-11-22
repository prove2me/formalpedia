-- Prove2me | solution 1 for CircuitComplexity.existQuantify_complexity_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:17:23.421807+00:00
-- url     : https://prove2.me/submissions/0b5629ce-8718-4665-a4e0-3dc539367f75

module
public import Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Nondeterminism
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_ShannonUpper
public import Definitions.Def_LeanPool_CircuitComplexity_Shannon
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism
public import Theorems.Thm_CircuitComplexity_existQuantify_complexity_le
public import Theorems.Thm_CircuitComplexity_existQuantify_complexity_shannon

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
variable {k m : Nat}
namespace CircuitComplexity
theorem _root_.solution [CompleteBasis Basis.andOr2]
    (f : BitString (k + m) → Bool) [NeZero m] (hm : 16 ≤ m) :
    Circuit.sizeComplexity Basis.andOr2 (existQuantify f) ≤
      min (2 ^ k * (Circuit.sizeComplexity Basis.andOr2 f + 1)) (18 * 2 ^ m / m) :=
  le_min (existQuantify_complexity_le f) (existQuantify_complexity_shannon f hm)
end CircuitComplexity
