-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.relation_finset_sum_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:18.694666+00:00
-- url     : https://prove2.me/submissions/e59f3d49-eb1f-4c33-bd78-035845cca8fa

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_basis
attribute [local simp] BooleanIsoperimetry.CoherentGap.realDot_basis



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution {n : ℕ} {α : Type}
    (set : Finset α) (relations : α → Relation n) (coordinate : Fin n) :
    (∑ index ∈ set, relations index) coordinate =
      ∑ index ∈ set, relations index coordinate := by
  classical
  induction set using Finset.induction_on with
  | empty => simp
  | @insert element set hnotMember inductionHypothesis =>
      simp [hnotMember, inductionHypothesis]
end BooleanIsoperimetry.CoherentGap
