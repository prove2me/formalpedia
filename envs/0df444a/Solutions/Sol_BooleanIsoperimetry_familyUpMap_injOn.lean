-- Prove2me | solution 1 for BooleanIsoperimetry.familyUpMap_injOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:25:07.608273+00:00
-- url     : https://prove2.me/submissions/a247ad0d-d9d5-4e07-bd72-2d70a41ca365

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
public import Theorems.Thm_BooleanIsoperimetry_blockReplace_recover
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
theorem _root_.solution {N : ℕ} (U V : Cube N) (𝒜 : Finset (Cube N)) :
    Set.InjOn (familyUpMap U V 𝒜) ↑𝒜 := by
  intro S hS T hT hST
  have hS' : S ∈ 𝒜 := Finset.mem_coe.mp hS
  have hT' : T ∈ 𝒜 := Finset.mem_coe.mp hT
  unfold familyUpMap at hST
  by_cases hSm : U ⊆ S ∧ Disjoint V S ∧ blockReplace U V S ∉ 𝒜
  · by_cases hTm : U ⊆ T ∧ Disjoint V T ∧ blockReplace U V T ∉ 𝒜
    · rw [if_pos hSm, if_pos hTm] at hST
      have hrec := congrArg (fun s => (s \ V) ∪ U) hST
      simpa only [blockReplace_recover hSm.1 hSm.2.1,
        blockReplace_recover hTm.1 hTm.2.1] using hrec
    · rw [if_pos hSm, if_neg hTm] at hST
      exact absurd (show blockReplace U V S ∈ 𝒜 by rw [hST]; exact hT') hSm.2.2
  · by_cases hTm : U ⊆ T ∧ Disjoint V T ∧ blockReplace U V T ∉ 𝒜
    · rw [if_neg hSm, if_pos hTm] at hST
      exact absurd (show blockReplace U V T ∈ 𝒜 by rw [← hST]; exact hS') hTm.2.2
    · rw [if_neg hSm, if_neg hTm] at hST
      exact hST
end BooleanIsoperimetry
