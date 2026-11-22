-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.negativeIndex_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:18.20571+00:00
-- url     : https://prove2.me/submissions/ed381255-9de8-44ff-b919-91a3db5b3543

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_triangular_strictMono
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_basis
attribute [local simp] BooleanIsoperimetry.CoherentGap.realDot_basis



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution (offset : ℕ) :
    Function.Injective (negativeIndex offset) := by
  intro first second hequal
  have hvalue := congrArg Fin.val hequal
  simp only [negativeIndex] at hvalue
  have hfirst := correction_deep_bound (dimension := offset + 2)
    (index := first.val) (by omega) first.isLt
  have hsecond := correction_deep_bound (dimension := offset + 2)
    (index := second.val) (by omega) second.isLt
  have htriangular :
      triangular first.val = triangular second.val := by
    omega
  apply Fin.ext
  exact triangular_strictMono.injective htriangular
end BooleanIsoperimetry.CoherentGap
