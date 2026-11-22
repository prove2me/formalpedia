-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.correctionFor_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:32.561802+00:00
-- url     : https://prove2.me/submissions/dce9ca92-339d-44a9-ab42-1de57dcf66c8

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_iteratedLift_basis_eq
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_castRelation_sub
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_castRelation_basis
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_basis
attribute [local simp] BooleanIsoperimetry.CoherentGap.realDot_basis



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution (offset : ℕ)
    (index : Fin (guide (offset + 2) - 1)) :
    (correctionFor offset index).target =
      basis (negativeIndex offset index) -
        basis (⟨index.val + 1, by
          have hdeep := correction_deep_bound (dimension := offset + 2)
            (index := index.val) (by omega) index.isLt
          omega⟩ : Fin (offset + 2)) := by
  unfold Correction.target
  rw [iteratedLift_basis_eq (hsteps := by simp [correctionFor])]
  rw [castRelation_sub, castRelation_basis, castRelation_basis]
  congr 1
  · apply congrArg basis
    apply Fin.ext
    suffices
        offset + 2 - triangular index.val - index.val - 3 + (index.val + 2) =
          offset + 2 - triangular index.val - 1 by
      simpa [correctionFor, negativeIndex]
    have hdeep := correction_deep_bound (dimension := offset + 2)
      (index := index.val) (by omega) index.isLt
    omega
end BooleanIsoperimetry.CoherentGap
