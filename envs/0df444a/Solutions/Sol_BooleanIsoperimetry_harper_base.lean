-- Prove2me | solution 1 for BooleanIsoperimetry.harper_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:39:55.648507+00:00
-- url     : https://prove2.me/submissions/0e459a63-da3b-447f-9de3-bd2ec11a9f35

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
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (A : Finset (Cube 0)) (k : ℕ) (hk : A.card = k) :
    (neighborhood 1 (simplicialInitSeg 0 k)).card ≤ (neighborhood 1 A).card := by
  subst hk
  fin_cases A <;>
    simp +decide [simplicialInitSeg, Finset.filter_singleton, rank, simplicialLt, simplicialLe]
end BooleanIsoperimetry
