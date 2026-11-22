-- Prove2me | solution 1 for BooleanIsoperimetry.coordinateDown_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:16:36.003665+00:00
-- url     : https://prove2.me/submissions/82320a36-cc8d-4fcc-a648-e6c44bcdd728

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
theorem _root_.solution {N : ℕ} (i : Fin N) (A : Finset (Cube N)) :
    IsCoordinateDown i A (coordinateDown i A) := by
  unfold IsCoordinateDown coordinateDown
  constructor
  · let A_kept := A.filter (fun x => i ∉ x ∨ erase x i ∈ A)
    let A_tomove := A.filter (fun x => i ∈ x ∧ erase x i ∉ A)
    have h_disj1 : Disjoint A_kept A_tomove := by
      rw [disjoint_iff_ne]
      intro x hx y hy hxy
      rw [mem_filter] at hx hy
      subst hxy
      rcases hx.2 with h1 | h2
      · exact h1 hy.2.1
      · exact hy.2.2 h2
    have h_union : A_kept ∪ A_tomove = A := by
      ext x
      simp only [mem_union]
      by_cases h1 : i ∈ x
      · by_cases h2 : erase x i ∈ A
        · aesop
        · aesop
      · aesop
    have h_inj : Set.InjOn (fun x => erase x i) (A_tomove : Set (Cube N)) := by
      intro x hx y hy eq
      rw [mem_coe, mem_filter] at hx hy
      have eq2 := congrArg (fun z => insert i z) eq
      simp only [insert_erase hx.2.1, insert_erase hy.2.1] at eq2
      exact eq2
    have h_card1 : (A_tomove.image (fun x => erase x i)).card = A_tomove.card :=
      card_image_of_injOn h_inj
    have h_disj2 : Disjoint A_kept (A_tomove.image (fun x => erase x i)) := by
      rw [disjoint_iff_ne]
      intro x hx y hy hxy
      rw [mem_filter] at hx
      rw [mem_image] at hy
      rcases hy with ⟨z, hz, rfl⟩
      subst hxy
      rw [mem_filter] at hz
      exact hz.2.2 hx.1
    rw [card_union_of_disjoint h_disj2, h_card1, ←card_union_of_disjoint h_disj1, h_union]
  · intro x
    simp only [mem_union, mem_image, mem_filter]
    constructor
    · rintro (⟨hxA, hxcond⟩ | ⟨y, ⟨hyA, hycond1, hycond2⟩, rfl⟩)
      · left; exact ⟨hxA, hxcond⟩
      · right
        exact ⟨by simp, hycond2, by rwa [insert_erase hycond1]⟩
    · rintro (⟨hxA, hxcond⟩ | ⟨hxi, hxA, hyA⟩)
      · left; exact ⟨hxA, hxcond⟩
      · right
        refine ⟨insert i x, ⟨hyA, by simp, ?_⟩, erase_insert hxi⟩
        · rwa [erase_insert hxi]
end BooleanIsoperimetry
