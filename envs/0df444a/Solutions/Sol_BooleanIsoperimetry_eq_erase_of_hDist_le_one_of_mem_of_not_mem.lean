-- Prove2me | solution 1 for BooleanIsoperimetry.eq_erase_of_hDist_le_one_of_mem_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:52.356556+00:00
-- url     : https://prove2.me/submissions/b09f1677-318f-4317-ba87-f0f71a8163a1

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {x y : Cube N} {i : Fin N}
    (h : hDist x y ≤ 1) (hix : i ∈ x) (hiy : i ∉ y) : y = x.erase i := by
  unfold hDist at h
  have hi : i ∈ symmDiff x y := by rw [mem_symmDiff]; tauto
  have heq : symmDiff x y = {i} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, fun j hj => ?_⟩
    by_contra h_ne
    have h_sub : {i, j} ⊆ symmDiff x y := by
      intro k hk
      rw [mem_insert, mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hi
      · exact hj
    have h_card : 2 ≤ (symmDiff x y).card := by
      have : ({i, j} : Finset (Fin N)).card = 2 := card_pair (ne_comm.mp h_ne)
      rw [← this]; exact card_le_card h_sub
    omega
  ext j
  by_cases hj : j = i
  · subst hj; simp [hix, hiy]
  · have hdiff : j ∉ symmDiff x y := by
      rw [heq]; exact fun h => hj (mem_singleton.mp h)
    simp only [mem_symmDiff] at hdiff
    have : j ∈ y ↔ j ∈ x := by tauto
    simp [hj, this]
end BooleanIsoperimetry
