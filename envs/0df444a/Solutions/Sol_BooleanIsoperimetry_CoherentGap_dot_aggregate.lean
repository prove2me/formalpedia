-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.dot_aggregate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:26:51.518437+00:00
-- url     : https://prove2.me/submissions/2fb9b5f7-b597-4396-acc7-bd7e69a08cf4

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_dot_add

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution {n : ℕ} (relations : List (Relation n)) (weights : Relation n) :
    dot (aggregate relations) weights =
      (relations.map fun relation => dot relation weights).sum := by
  induction relations with
  | nil =>
      simp [aggregate, dot]
  | cons relation relations inductionHypothesis =>
      change dot (relation + aggregate relations) weights =
        dot relation weights +
          (relations.map fun tailRelation => dot tailRelation weights).sum
      rw [dot_add, inductionHypothesis]
end BooleanIsoperimetry.CoherentGap
