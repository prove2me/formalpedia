-- Prove2me | solution 1 for BooleanIsoperimetry.gShiftIntervalCount_eq_H_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:40.369476+00:00
-- url     : https://prove2.me/submissions/cff61806-1f1e-4b11-b925-93afaa9db960

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
public import Theorems.Thm_BooleanIsoperimetry_H_eq_gShift_count
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n lo hi : ℕ) (hlohi : lo ≤ hi) :
    gShiftIntervalCount n lo hi = H n hi - H n lo := by
  rw [gShiftIntervalCount, H_eq_gShift_count n hi, H_eq_gShift_count n lo]
  let Ahi : Finset (Cube n) :=
    Finset.univ.filter (fun v : Cube n => rank (gShift v) < hi)
  let Alo : Finset (Cube n) :=
    Finset.univ.filter (fun v : Cube n => rank (gShift v) < lo)
  let Aint : Finset (Cube n) :=
    Finset.univ.filter (fun v : Cube n => lo ≤ rank (gShift v) ∧ rank (gShift v) < hi)
  have hsplit : Ahi = Alo ∪ Aint := by
    ext v
    simp [Ahi, Alo, Aint]
    omega
  have hdisj : Disjoint Alo Aint := by
    rw [Finset.disjoint_left]
    intro v hvlo hvint
    simp [Alo] at hvlo
    simp [Aint] at hvint
    omega
  have hcard : Ahi.card = Alo.card + Aint.card := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
  change Aint.card = Ahi.card - Alo.card
  omega
end BooleanIsoperimetry
