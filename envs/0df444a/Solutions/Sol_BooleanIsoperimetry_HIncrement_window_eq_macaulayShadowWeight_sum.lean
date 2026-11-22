-- Prove2me | solution 1 for BooleanIsoperimetry.HIncrement_window_eq_macaulayShadowWeight_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:39:15.435435+00:00
-- url     : https://prove2.me/submissions/f8cb95c5-c1be-4e9d-9a46-00068bdf53b4

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
public import Theorems.Thm_BooleanIsoperimetry_HIncrement_eq_macaulayShadowWeight
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_rank_image_eq
public import Theorems.Thm_BooleanIsoperimetry_rank_injective
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution
    (n lo hi : ℕ) (hhi : hi ≤ 2 ^ n) :
    (∑ i ∈ Finset.Ico lo hi, HIncrement n i) =
      ∑ w ∈ (Finset.univ.filter (fun w : Cube n => lo ≤ rank w ∧ rank w < hi)),
        macaulayShadowWeight w := by
  let S : Finset (Cube n) :=
    Finset.univ.filter (fun w : Cube n => lo ≤ rank w ∧ rank w < hi)
  have himage : S.image rank = Finset.Ico lo hi := by
    ext i
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ico]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hiI
      have hi_range : i ∈ Finset.range (2 ^ n) :=
        Finset.mem_range.mpr (lt_of_lt_of_le hiI.2 hhi)
      obtain ⟨w, _hwuniv, hrank⟩ :=
        Finset.mem_image.mp (by
          simpa [rank_image_eq] using hi_range :
            i ∈ Finset.univ.image (@rank n))
      exact ⟨w, by simpa [hrank] using hiI, hrank⟩
  rw [← himage]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro w _hwS
    exact HIncrement_eq_macaulayShadowWeight (rank w) w rfl
  · intro x _hx y _hy hxy
    exact rank_injective hxy
end BooleanIsoperimetry
