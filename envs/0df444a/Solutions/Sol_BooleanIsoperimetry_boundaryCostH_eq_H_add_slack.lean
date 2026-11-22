-- Prove2me | solution 1 for BooleanIsoperimetry.boundaryCostH_eq_H_add_slack
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:38:37.735629+00:00
-- url     : https://prove2.me/submissions/b909a7b8-b46c-47ea-b44f-acf93e781140

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (N a b : ℕ) :
    boundaryCostH N a b =
      H N a + H N b + (b - H N a) + (a - H N b) := by
  unfold boundaryCostH
  omega
end BooleanIsoperimetry
