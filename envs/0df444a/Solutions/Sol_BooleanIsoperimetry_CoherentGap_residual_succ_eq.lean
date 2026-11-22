-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.residual_succ_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:44.918134+00:00
-- url     : https://prove2.me/submissions/1ea5b4f4-19bc-41cb-bed1-7e8a7b261d3e

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
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_conwayGuyDifference_succ
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_conwayGuyHeight_succ


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution {width dimension : ℕ}
    (hdimension : 0 < dimension)
    (hwidth : width ≤ dimension)
    (hguide : guide (dimension + 1) = width) :
    residual width (dimension + 1) = residual width dimension := by
  have hheight :
      ∀ index : Fin width,
        conwayGuyHeight (dimension + 1 - index.val - 1) =
          conwayGuyHeight (dimension - index.val - 1) +
            conwayGuyDifference (dimension - index.val - 1) := by
    intro index
    have hindex : index.val < dimension := index.isLt.trans_le hwidth
    have hsucc :
        dimension + 1 - index.val - 1 =
          (dimension - index.val - 1) + 1 := by
      omega
    rw [hsucc, conwayGuyHeight_succ]
  rw [residual, residual, conwayGuyHeight_succ]
  simp_rw [hheight]
  rw [Finset.sum_add_distrib]
  have hdifference :
      conwayGuyDifference dimension =
        ∑ index : Fin width,
          (conwayGuyDifference (dimension - index.val - 1) : ℤ) := by
    obtain ⟨previous, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (by omega : dimension ≠ 0)
    rw [conwayGuyDifference_succ, hguide]
    push_cast
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro index hindex
    have hargument :
        previous.succ - index.val - 1 = previous - index.val := by
      omega
    rw [hargument]
  rw [hdifference]
  ring
end BooleanIsoperimetry.CoherentGap
