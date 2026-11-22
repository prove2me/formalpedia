-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.principal_entry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:42.985859+00:00
-- url     : https://prove2.me/submissions/59e3c197-56f4-42d9-890d-fe327c4a096f

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_positiveIndex_injective
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_negativeIndex_injective
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_positiveIndex_ne_negativeIndex
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_sum_basis_apply
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_basis
attribute [local simp] BooleanIsoperimetry.CoherentGap.realDot_basis



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution (offset : ℕ) (coordinate : Fin (offset + 2)) :
    principal offset coordinate = -1 ∨
      principal offset coordinate = 0 ∨
      principal offset coordinate = 1 := by
  classical
  rw [principal, Pi.sub_apply]
  rw [sum_basis_apply (positiveIndex offset) (positiveIndex_injective offset)]
  rw [sum_basis_apply (negativeIndex offset) (negativeIndex_injective offset)]
  by_cases hpositive :
      coordinate ∈ Finset.univ.image (positiveIndex offset)
  · have hnegative :
        coordinate ∉ Finset.univ.image (negativeIndex offset) := by
      intro hmember
      rcases Finset.mem_image.mp hpositive with ⟨positive, _, hpositiveEqual⟩
      rcases Finset.mem_image.mp hmember with ⟨negative, _, hnegativeEqual⟩
      exact positiveIndex_ne_negativeIndex offset positive negative
        (hpositiveEqual.trans hnegativeEqual.symm)
    simp [hpositive, hnegative]
  · by_cases hnegative :
        coordinate ∈ Finset.univ.image (negativeIndex offset)
    · simp [hpositive, hnegative]
    · simp [hpositive, hnegative]
end BooleanIsoperimetry.CoherentGap
