-- Prove2me | solution 1 for BooleanIsoperimetry.H_le_binomPrefix_of_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:45:03.965201+00:00
-- url     : https://prove2.me/submissions/fbcacd10-8071-4df9-84f8-79bc77b3de38

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
public import Theorems.Thm_BooleanIsoperimetry_H_binomPrefix
public import Theorems.Thm_BooleanIsoperimetry_H_mono


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (N a b r : ℕ)
    (hb : b ≤ binomPrefix N (r + 1)) (hcase : a ≤ H N b) :
    a ≤ binomPrefix N (r + 2) := by
  calc a ≤ H N b := hcase
    _ ≤ H N (binomPrefix N (r + 1)) := H_mono hb
    _ = binomPrefix N (r + 2) := H_binomPrefix N (r + 1) (by omega)
end BooleanIsoperimetry
