-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.principal_coordinateSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:01.32459+00:00
-- url     : https://prove2.me/submissions/044c663b-4df5-4b98-9f3f-895b4a8bfaff

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_coordinateSum_sub
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_coordinateSum_finset_sum
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_basis
attribute [local simp] BooleanIsoperimetry.CoherentGap.realDot_basis



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution (offset : ℕ) :
    coordinateSum (principal offset) = 1 := by
  rw [principal, coordinateSum_sub]
  simp only [coordinateSum_finset_sum, coordinateSum_basis,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpositive := guide_pos (dimension := offset + 2) (by omega)
  omega
end BooleanIsoperimetry.CoherentGap
