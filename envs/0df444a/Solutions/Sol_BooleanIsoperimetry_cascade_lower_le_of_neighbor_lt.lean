-- Prove2me | solution 1 for BooleanIsoperimetry.cascade_lower_le_of_neighbor_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:48.732751+00:00
-- url     : https://prove2.me/submissions/577283fa-ef7c-4279-8938-65fedc307226

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
public import Theorems.Thm_BooleanIsoperimetry_H_mono
public import Theorems.Thm_BooleanIsoperimetry_cascade_p_le_H_q
public import Theorems.Thm_BooleanIsoperimetry_cascade_split_add


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n a b p q : ℕ}
    (hcasc : CascadeSplit (n + 1) (a + b) p q) (hq_pos : 1 ≤ q)
    (hcase : H (n + 1) b < a) : p ≤ a := by
  by_contra h
  push Not at h
  have hsum : p + q = a + b := cascade_split_add hcasc
  have hqb : q < b := by omega
  have hpHq : p ≤ H (n + 1) q := cascade_p_le_H_q hcasc hq_pos
  have hmono : H (n + 1) q ≤ H (n + 1) b := H_mono (le_of_lt hqb)
  omega
end BooleanIsoperimetry
