-- Prove2me | solution 1 for BooleanIsoperimetry.interleaving_boundaryCost_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:05:02.977137+00:00
-- url     : https://prove2.me/submissions/622a7e2e-e2a2-41f5-91c1-b8b78b9fa5fe

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
public import Theorems.Thm_BooleanIsoperimetry_harper_core
public import Theorems.Thm_BooleanIsoperimetry_H_succ_cascade


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution
    {n p q a b : ℕ} (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n)
    (h_inter : CascadeInterleaves n p q a b) :
    boundaryCost n p q ≤ boundaryCost n a b := by
  obtain ⟨h_casc, _⟩ := h_inter
  have hpq : boundaryCost n p q = H (n + 1) (a + b) := by
    rw [boundaryCost]; exact (H_succ_cascade h_casc).symm
  rw [hpq]
  exact harper_core n a b ha hb
end BooleanIsoperimetry
