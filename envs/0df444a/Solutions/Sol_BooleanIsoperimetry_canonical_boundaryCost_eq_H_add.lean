-- Prove2me | solution 1 for BooleanIsoperimetry.canonical_boundaryCost_eq_H_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:37.534963+00:00
-- url     : https://prove2.me/submissions/45ccc229-ed64-44e3-8eb7-bd09551fd768

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
public import Theorems.Thm_BooleanIsoperimetry_H_ge_self
public import Theorems.Thm_BooleanIsoperimetry_cascade_p_le_H_q
public import Theorems.Thm_BooleanIsoperimetry_cascade_q_le_p


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution
    {n k p q : ℕ} (hp : p ≤ 2 ^ n) (_hq : q ≤ 2 ^ n) (hq_pos : 1 ≤ q)
    (h_casc : CascadeSplit n k p q) :
    max (H n p) q + max (H n q) p = H n p + H n q := by
  have h1 : q ≤ p := cascade_q_le_p h_casc
  have h2 : p ≤ H n p := H_ge_self n p hp
  have h3 : q ≤ H n p := le_trans h1 h2
  have h4 : p ≤ H n q := cascade_p_le_H_q h_casc hq_pos
  have max1 : max (H n p) q = H n p := max_eq_left h3
  have max2 : max (H n q) p = H n q := max_eq_left h4
  rw [max1, max2]
end BooleanIsoperimetry
