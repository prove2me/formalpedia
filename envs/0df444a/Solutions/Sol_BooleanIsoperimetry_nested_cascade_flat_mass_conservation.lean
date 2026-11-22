-- Prove2me | solution 1 for BooleanIsoperimetry.nested_cascade_flat_mass_conservation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:42:03.59105+00:00
-- url     : https://prove2.me/submissions/1fea14bf-a936-4f2a-a68d-dccea2c654b4

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Theorems.Thm_BooleanIsoperimetry_nested_cascade_mass_conservation

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n a b p q p0 p1 q0 q1 a0 a1 b0 b1 : ℕ}
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hp_split : CascadeSplit n p p0 p1)
    (hq_split : CascadeSplit n q q0 q1)
    (ha_split : CascadeSplit n a a0 a1)
    (hb_split : CascadeSplit n b b0 b1) :
    p0 + p1 + q0 + q1 = a0 + a1 + b0 + b1 := by
  have h := nested_cascade_mass_conservation hcasc hp_split hq_split ha_split hb_split
  omega
end BooleanIsoperimetry
