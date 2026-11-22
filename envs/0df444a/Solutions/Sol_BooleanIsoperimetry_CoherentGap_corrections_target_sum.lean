-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.corrections_target_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:29:11.783846+00:00
-- url     : https://prove2.me/submissions/4a21712f-56f2-4c24-83eb-1f057235f44d

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_correctionFor_target
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_basis
attribute [local simp] BooleanIsoperimetry.CoherentGap.realDot_basis



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution (offset : ℕ) :
    ((corrections offset).map Correction.target).sum =
      ∑ index : Fin (guide (offset + 2) - 1),
        (basis (negativeIndex offset index) -
          basis (⟨index.val + 1, by
            have hdeep := correction_deep_bound (dimension := offset + 2)
              (index := index.val) (by omega) index.isLt
            omega⟩ : Fin (offset + 2))) := by
  simp [corrections, List.sum_ofFn, correctionFor_target]
end BooleanIsoperimetry.CoherentGap
