-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.dot_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:18.836139+00:00
-- url     : https://prove2.me/submissions/916aec37-d0bd-4dd1-bd2d-db8a36a3d373

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
theorem _root_.solution {n : ℕ} (first second weights : Relation n) :
    dot (first + second) weights = dot first weights + dot second weights := by
  simp [dot, add_mul, Finset.sum_add_distrib]
end BooleanIsoperimetry.CoherentGap
