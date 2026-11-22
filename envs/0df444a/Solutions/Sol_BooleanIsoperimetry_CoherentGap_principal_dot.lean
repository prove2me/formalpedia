-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.principal_dot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:18.731878+00:00
-- url     : https://prove2.me/submissions/58e9d0c9-34a9-4c1d-b3df-3195044b11eb

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_dot_sub
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_dot_finset_sum
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_basis
attribute [local simp] BooleanIsoperimetry.CoherentGap.realDot_basis



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution (offset : ℕ)
    (hblock :
      conwayGuyHeight (offset + 2) -
          ∑ index : Fin (guide (offset + 2)),
            conwayGuyHeight (offset + 2 - index.val - 1) +
        ∑ index : Fin (guide (offset + 2) - 1),
          conwayGuyHeight (triangular index.val) = 1) :
    dot (principal offset) (conwayGuyArithmetic.weights (offset + 2)) = 1 := by
  rw [principal, dot_sub]
  simp only [dot_finset_sum, dot_basis,
    ConwayGuyArithmetic.weights, positiveIndex, negativeIndex]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  push_cast
  have hpositive := guide_pos (dimension := offset + 2) (by omega)
  have hnegativeIndex :
      ∀ index : Fin (guide (offset + 2) - 1),
        offset + 1 -
            (offset + 2 - triangular index.val - 1) =
          triangular index.val := by
    intro index
    have hdeep := correction_deep_bound (dimension := offset + 2)
      (index := index.val) (by omega) index.isLt
    omega
  simp_rw [hnegativeIndex]
  have hpositiveIndex :
      ∀ index : Fin (guide (offset + 2)),
        offset + 2 - index.val - 1 = offset + 1 - index.val := by
    intro index
    omega
  simp_rw [hpositiveIndex] at hblock
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hguide :
      (guide (offset + 2) : ℤ) =
        (guide (offset + 2) - 1 : ℕ) + 1 := by
    omega
  rw [hguide]
  ring_nf
  simpa [conwayGuyArithmetic, Nat.add_comm] using hblock
end BooleanIsoperimetry.CoherentGap
