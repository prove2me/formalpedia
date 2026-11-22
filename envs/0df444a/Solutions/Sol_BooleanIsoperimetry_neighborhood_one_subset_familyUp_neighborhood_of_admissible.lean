-- Prove2me | solution 1 for BooleanIsoperimetry.neighborhood_one_subset_familyUp_neighborhood_of_admissible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:38:48.000963+00:00
-- url     : https://prove2.me/submissions/81ee3ba4-150a-40b0-8777-f6119c3c304e

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_one_eq_self_union_shadow_upShadow
public import Theorems.Thm_BooleanIsoperimetry_familyUp_subset_familyUp
public import Theorems.Thm_BooleanIsoperimetry_familyUp_shadow_subset
public import Theorems.Thm_BooleanIsoperimetry_familyUp_upShadow_subset
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ}
    {A : Finset (Cube N)} {U V : Cube N}
    (hd : Disjoint U V)
    (hadm : IsUVAdmissibleForFamily A U V)
    (hadm' : IsUVAdmissibleForFamily (Aᶜˢ) V U) :
    neighborhood 1 (familyUp U V A) ⊆ familyUp U V (neighborhood 1 A) := by
  rw [neighborhood_one_eq_self_union_shadow_upShadow,
    neighborhood_one_eq_self_union_shadow_upShadow]
  intro x hx
  simp only [Finset.mem_union] at hx ⊢
  rcases hx with (hxA | hxSh) | hxUp
  · have : x ∈ familyUp U V A := hxA
    have H_sub : A ⊆ A ∪ shadow A ∪ upShadow A := by
      intro y hy
      simp only [Finset.mem_union]
      tauto
    exact familyUp_subset_familyUp hd H_sub this
  · have : x ∈ shadow (familyUp U V A) := hxSh
    have H : x ∈ familyUp U V (shadow A) := familyUp_shadow_subset hd hadm this
    have H_sub : shadow A ⊆ A ∪ shadow A ∪ upShadow A := by
      intro y hy
      simp only [Finset.mem_union]
      tauto
    exact familyUp_subset_familyUp hd H_sub H
  · have : x ∈ upShadow (familyUp U V A) := hxUp
    have H : x ∈ familyUp U V (upShadow A) := familyUp_upShadow_subset hd hadm' this
    have H_sub : upShadow A ⊆ A ∪ shadow A ∪ upShadow A := by
      intro y hy
      simp only [Finset.mem_union]
      tauto
    exact familyUp_subset_familyUp hd H_sub H
end BooleanIsoperimetry
