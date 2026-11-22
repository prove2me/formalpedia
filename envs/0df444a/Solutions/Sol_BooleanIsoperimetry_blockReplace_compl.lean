-- Prove2me | solution 1 for BooleanIsoperimetry.blockReplace_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:02.928553+00:00
-- url     : https://prove2.me/submissions/fbd15912-8e7c-4fc4-b0bf-f8ad460a5e03

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
theorem _root_.solution {N : ℕ} {U V : Cube N} (hd : Disjoint U V) (S : Cube N) :
    (blockReplace U V S)ᶜ = blockReplace V U Sᶜ := by
  unfold blockReplace
  have hUV := Finset.disjoint_left.mp hd
  ext x
  simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · intro h
    by_cases hxU : x ∈ U
    · exact Or.inr hxU
    · exact Or.inl ⟨fun hxS => h (Or.inl ⟨hxS, hxU⟩), fun hxV => h (Or.inr hxV)⟩
  · rintro (⟨hxnS, hxnV⟩ | hxU)
    · rintro (⟨hxS, _⟩ | hxV)
      · exact hxnS hxS
      · exact hxnV hxV
    · rintro (⟨_, hxnU⟩ | hxV)
      · exact hxnU hxU
      · exact hUV hxU hxV
end BooleanIsoperimetry
