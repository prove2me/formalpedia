-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.coordinateSum_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:17.429817+00:00
-- url     : https://prove2.me/submissions/aa90688d-091f-4ae2-9b75-f931ba13128f

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
    (set : Finset α) (relations : α → Relation n) :
    coordinateSum (∑ index ∈ set, relations index) =
      ∑ index ∈ set, coordinateSum (relations index) := by
  classical
  induction set using Finset.induction_on with
  | empty => simp [coordinateSum]
  | @insert element set hnotMember inductionHypothesis =>
      simp [hnotMember, coordinateSum_add, inductionHypothesis]
end BooleanIsoperimetry.CoherentGap
