-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.conwayGuyDifference_eq_height_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:32.926783+00:00
-- url     : https://prove2.me/submissions/0b6a2cbb-7e66-4a3e-b300-1dc09102516b

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
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_guide_lt_dimension
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_conwayGuyDifference_succ
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_reverse_difference_sum

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution (dimension : ℕ)
    (hdimension : 0 < dimension) :
    (conwayGuyDifference dimension : ℤ) =
      conwayGuyHeight dimension -
        conwayGuyHeight (dimension - guide (dimension + 1)) := by
  obtain ⟨previous, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : dimension ≠ 0)
  rw [conwayGuyDifference_succ]
  push_cast
  rw [← Fin.sum_univ_eq_sum_range]
  have hwindow :=
    reverse_difference_sum previous.succ (guide (previous.succ + 1))
      (guide_lt_dimension (dimension := previous.succ + 1) (by omega) |>
        fun h => by omega)
  have hargument :
      ∀ index : Fin (guide (previous.succ + 1)),
        previous - index.val =
          previous.succ - index.val - 1 := by
    intro index
    omega
  simp_rw [hargument]
  exact hwindow
end BooleanIsoperimetry.CoherentGap
