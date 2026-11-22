-- Prove2me | solution 1 for BooleanIsoperimetry.upperShadowVal_eq_card_upperLayerShadow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:39:39.773805+00:00
-- url     : https://prove2.me/submissions/94c1f011-76a0-4951-a2b3-9b87c4eed797

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Combinatorics.Colex
public import Mathlib.Combinatorics.SetFamily.Shadow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Combinatorics.SetFamily.KruskalKatona
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_binomPrefix
public import Theorems.Thm_BooleanIsoperimetry_simplicialInitSeg_decomp
public import Theorems.Thm_BooleanIsoperimetry_upShadow_subset_neighborhood
public import Theorems.Thm_BooleanIsoperimetry_hDist_eq_one_of_card_diff
public import Theorems.Thm_BooleanIsoperimetry_card_le_of_hDist_le_one
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_union
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_card_le_rank
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_le_two_pow
public import Theorems.Thm_BooleanIsoperimetry_card_simplicialInitSeg
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_rank_lt_binomPrefix_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open Finset.Colex
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N r t : ℕ} (hr : 1 ≤ r)
    (ht : t ≤ Nat.choose N r) :
    upperShadowVal N r t = (upperLayerShadow N r (layerInitSeg N r t)).card := by
  unfold upperShadowVal
  unfold H
  rw [simplicialInitSeg_decomp ht]
  rw [neighborhood_union]
  rw [neighborhood_binomPrefix hr]
  have h_disj : Disjoint (simplicialInitSeg N (binomPrefix N (r + 1)))
      (upperLayerShadow N r (layerInitSeg N r t)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [simplicialInitSeg, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [upperLayerShadow, Finset.mem_filter] at hy
    have h_card : x.card = r + 1 := hy.2
    have h_rank_ge : binomPrefix N (r + 1) ≤ rank x := by
      simpa [h_card] using binomPrefix_card_le_rank x
    omega
  have h_union : simplicialInitSeg N (binomPrefix N (r + 1)) ∪ neighborhood 1 (layerInitSeg N r t) =
      simplicialInitSeg N (binomPrefix N (r + 1)) ∪ upperLayerShadow N r (layerInitSeg N r t) := by
    ext x
    simp only [Finset.mem_union, upperLayerShadow, Finset.mem_filter]
    constructor
    · rintro (hx | hx_nb)
      · left; exact hx
      · have h_card_le : x.card ≤ r + 1 := by
          rcases mem_neighborhood_iff.mp hx_nb with ⟨u, hu, hdist⟩
          have h_u_card : u.card = r := by
            simp only [layerInitSeg, Finset.mem_filter] at hu
            exact hu.2
          exact card_le_of_hDist_le_one h_u_card hdist
        rcases lt_or_eq_of_le h_card_le with hlt | heq
        · left
          have h_rank_lt : rank x < binomPrefix N (r + 1) :=
            (rank_lt_binomPrefix_iff (n := N) (c := r + 1) x).mpr hlt
          simp only [simplicialInitSeg, Finset.mem_filter, Finset.mem_univ, true_and]
          exact h_rank_lt
        · right
          refine ⟨?_, heq⟩
          rw [Finset.mem_upShadow_iff]
          rcases mem_neighborhood_iff.mp hx_nb with ⟨u, hu, hdist⟩
          have h_u_card : u.card = r := by
            simp only [layerInitSeg, Finset.mem_filter] at hu
            exact hu.2
          rcases hDist_eq_one_of_card_diff h_u_card heq hdist with ⟨hsub, hdiff⟩
          have h_exists := Finset.card_eq_one.mp hdiff
          rcases h_exists with ⟨a, ha⟩
          have h_a_not_mem : a ∉ u := by
            have h_a_in : a ∈ x \ u := by rw [ha]; exact Finset.mem_singleton_self a
            exact (Finset.mem_sdiff.mp h_a_in).2
          have heq_insert : x = insert a u := by
            ext y
            constructor
            · intro hy
              by_cases hyu : y ∈ u
              · exact Finset.mem_insert_of_mem hyu
              · have h_y_in : y ∈ x \ u := Finset.mem_sdiff.mpr ⟨hy, hyu⟩
                rw [ha, Finset.mem_singleton] at h_y_in
                rw [h_y_in]
                exact Finset.mem_insert_self a u
            · rintro hy
              rcases Finset.mem_insert.mp hy with hy_eq | hyu
              · rw [hy_eq]
                have h_a_in : a ∈ x \ u := by rw [ha]; exact Finset.mem_singleton_self a
                exact (Finset.mem_sdiff.mp h_a_in).1
              · exact hsub hyu
          exact ⟨u, hu, a, h_a_not_mem, heq_insert.symm⟩
    · rintro (hx | ⟨hx_up, _⟩)
      · left; exact hx
      · right
        apply upShadow_subset_neighborhood (layerInitSeg N r t)
        · intro y hy
          simp only [layerInitSeg, Finset.mem_filter] at hy
          exact hy.2
        · exact hx_up
  rw [h_union]
  rw [Finset.card_union_of_disjoint h_disj]
  have h_card_simp :
      (simplicialInitSeg N (binomPrefix N (r + 1))).card = binomPrefix N (r + 1) := by
    rw [card_simplicialInitSeg]
    have h_le : binomPrefix N (r + 1) ≤ 2^N := binomPrefix_le_two_pow N (r + 1)
    omega
  rw [h_card_simp]
  omega
end BooleanIsoperimetry
