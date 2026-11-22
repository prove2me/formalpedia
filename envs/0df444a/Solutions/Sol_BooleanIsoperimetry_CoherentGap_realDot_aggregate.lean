-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.realDot_aggregate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:27.899796+00:00
-- url     : https://prove2.me/submissions/92a767bf-e691-44cc-8208-ee558505a7d9

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_add

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution {n : ℕ} (relations : List (Relation n))
    (candidate : Fin n → ℝ) :
    realDot (aggregate relations) candidate =
      (relations.map fun relation => realDot relation candidate).sum := by
  induction relations with
  | nil =>
      simp [aggregate, realDot]
  | cons relation relations inductionHypothesis =>
      change realDot (relation + aggregate relations) candidate =
        realDot relation candidate +
          (relations.map fun tailRelation => realDot tailRelation candidate).sum
      rw [realDot_add, inductionHypothesis]
end BooleanIsoperimetry.CoherentGap
