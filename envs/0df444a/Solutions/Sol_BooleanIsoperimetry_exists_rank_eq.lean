-- Prove2me | solution 1 for BooleanIsoperimetry.exists_rank_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:29:30.705798+00:00
-- url     : https://prove2.me/submissions/923303fd-d989-40ab-a84a-5ce199fb9cbf

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Theorems.Thm_BooleanIsoperimetry_rank_image_eq


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n j : ℕ} (hj : j < 2 ^ n) : ∃ w : Cube n, rank w = j := by
  have hmem : j ∈ Finset.image (@rank n) Finset.univ := by
    rw [rank_image_eq]; exact Finset.mem_range.mpr hj
  obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hmem
  exact ⟨w, hw⟩
end BooleanIsoperimetry
