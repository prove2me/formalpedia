-- Prove2me | solution 1 for BooleanIsoperimetry.coordinateUp_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:18:56.354221+00:00
-- url     : https://prove2.me/submissions/215d938b-3f19-4e78-807a-7dc3c845ee84

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
    IsCoordinateUp i A (coordinateUp i A) := by
  unfold IsCoordinateUp coordinateUp
  constructor
  · let A_kept := A.filter (fun x => i ∈ x ∨ insert i x ∈ A)
    let A_tomove := A.filter (fun x => i ∉ x ∧ insert i x ∉ A)
    have h_disj1 : Disjoint A_kept A_tomove := by
      rw [disjoint_iff_ne]
      intro x hx y hy hxy
      rw [mem_filter] at hx hy
      subst hxy
      rcases hx.2 with h1 | h2
      · exact hy.2.1 h1
      · exact hy.2.2 h2
    have h_union : A_kept ∪ A_tomove = A := by
      ext x
      simp only [mem_union]
      by_cases h1 : i ∈ x
      · aesop
      · by_cases h2 : insert i x ∈ A
        · aesop
        · aesop
    have h_inj : Set.InjOn (fun x => insert i x) (A_tomove : Set (Cube N)) := by
      intro x hx y hy eq
      rw [mem_coe, mem_filter] at hx hy
      have eq2 := congrArg (fun z => erase z i) eq
      simp only [erase_insert hx.2.1, erase_insert hy.2.1] at eq2
      exact eq2
    have h_card1 : (A_tomove.image (fun x => insert i x)).card = A_tomove.card :=
      card_image_of_injOn h_inj
    have h_disj2 : Disjoint A_kept (A_tomove.image (fun x => insert i x)) := by
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
        exact ⟨mem_insert_self i y, hycond2, by rwa [erase_insert hycond1]⟩
    · rintro (⟨hxA, hxcond⟩ | ⟨hxi, hxA, hyA⟩)
      · left; exact ⟨hxA, hxcond⟩
      · right
        refine ⟨erase x i, ⟨hyA, by simp, ?_⟩, insert_erase hxi⟩
        · rwa [insert_erase hxi]
end BooleanIsoperimetry
