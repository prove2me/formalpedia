-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.realDot_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:26:59.246238+00:00
-- url     : https://prove2.me/submissions/e7b0222a-3796-4daa-b1ea-baf5b83b6eb1

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution {n : ℕ} (first second : Relation n)
    (candidate : Fin n → ℝ) :
    realDot (first + second) candidate =
      realDot first candidate + realDot second candidate := by
  simp [realDot, add_mul, Finset.sum_add_distrib]
end BooleanIsoperimetry.CoherentGap
