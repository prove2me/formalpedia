-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.reverse_difference_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:49.635002+00:00
-- url     : https://prove2.me/submissions/f0207329-cb5f-4212-9524-b28feecd3a84

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyHeight
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_conwayGuyHeight_succ
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_basis
attribute [local simp] BooleanIsoperimetry.CoherentGap.realDot_basis



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution (dimension : ℕ) :
    ∀ width : ℕ, width ≤ dimension →
      (∑ index : Fin width,
          (conwayGuyDifference (dimension - index.val - 1) : ℤ)) =
        conwayGuyHeight dimension -
          conwayGuyHeight (dimension - width)
  | 0, _ => by simp
  | width + 1, hwidth => by
      have hdimension : 0 < dimension := by omega
      obtain ⟨previous, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (by omega : dimension ≠ 0)
      rw [Fin.sum_univ_succ]
      have inductionHypothesis :=
        solution previous width (by omega)
      have hargument :
          ∀ index : Fin width,
            previous.succ - index.succ.val - 1 =
              previous - index.val - 1 := by
        intro index
        change previous + 1 - (index.val + 1) - 1 =
          previous - index.val - 1
        omega
      simp_rw [hargument]
      rw [inductionHypothesis, conwayGuyHeight_succ]
      have htail :
          previous.succ - (width + 1) = previous - width := by
        omega
      rw [htail]
      have hzero :
          previous.succ - (0 : Fin (width + 1)).val - 1 = previous := by
        simp
      rw [hzero]
      ring
end BooleanIsoperimetry.CoherentGap
