-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.dot_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:34.397388+00:00
-- url     : https://prove2.me/submissions/04b716c8-7660-4229-b22e-f33e29860a6b

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_dot_add
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_basis
attribute [local simp] BooleanIsoperimetry.CoherentGap.realDot_basis



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution {n : ℕ} {α : Type}
    (set : Finset α) (relations : α → Relation n) (weights : Relation n) :
    dot (∑ index ∈ set, relations index) weights =
      ∑ index ∈ set, dot (relations index) weights := by
  classical
  induction set using Finset.induction_on with
  | empty => simp [dot]
  | @insert element set hnotMember inductionHypothesis =>
      simp [hnotMember, dot_add, inductionHypothesis]
end BooleanIsoperimetry.CoherentGap
