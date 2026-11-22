-- Prove2me | solution 1 for BooleanIsoperimetry.macaulay_optimization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:06:10.789065+00:00
-- url     : https://prove2.me/submissions/26767f14-2578-4efc-b5f7-069fe4865272

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
public import Theorems.Thm_BooleanIsoperimetry_H_inequality_core
public import Theorems.Thm_BooleanIsoperimetry_H_succ_cascade


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n a b p q : ℕ} (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n)
    (h_casc : CascadeSplit n (a + b) p q) :
    max (H n p) q + max (H n q) p ≤ max (H n a) b + max (H n b) a := by
  rw [← H_succ_cascade h_casc]
  exact H_inequality_core n a b ha hb
end BooleanIsoperimetry
