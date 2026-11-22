-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.positiveIndex_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:17.787738+00:00
-- url     : https://prove2.me/submissions/54e648e5-d282-4c0f-8e51-e96c00f8e0b2

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
theorem _root_.solution (offset : ℕ) :
    Function.Injective (positiveIndex offset) := by
  intro first second hequal
  apply Fin.ext
  simpa [positiveIndex] using congrArg Fin.val hequal
end BooleanIsoperimetry.CoherentGap
