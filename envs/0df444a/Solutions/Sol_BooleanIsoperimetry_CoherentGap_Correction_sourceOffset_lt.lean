-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.Correction.sourceOffset_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:40:16.628819+00:00
-- url     : https://prove2.me/submissions/ff4011c8-8c94-47c5-a987-4da1f6986726

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
namespace Correction
theorem _root_.solution {offset : ℕ}
    (correction : Correction (offset + 2)) :
    correction.sourceOffset < offset + 1 := by
  have := correction.sourceDimension_lt
  omega
end Correction
end BooleanIsoperimetry.CoherentGap
