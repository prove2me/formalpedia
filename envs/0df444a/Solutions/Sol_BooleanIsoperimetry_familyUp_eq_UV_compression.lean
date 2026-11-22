-- Prove2me | solution 1 for BooleanIsoperimetry.familyUp_eq_UV_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:01.603602+00:00
-- url     : https://prove2.me/submissions/932f29da-fd8e-4ac9-a22a-6070de468d8d

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
public import Theorems.Thm_BooleanIsoperimetry_compress_VU_eq_blockReplace

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (A : Finset (Cube N)) {U V : Cube N}
    (hd : Disjoint U V) :
    familyUp U V A = UV.compression V U A := by
  ext a
  rw [familyUp, Finset.mem_image, UV.mem_compression]
  constructor
  · rintro ⟨S, hS, rfl⟩
    unfold familyUpMap
    by_cases hc : U ⊆ S ∧ Disjoint V S ∧ blockReplace U V S ∉ A
    · rw [if_pos hc]
      exact Or.inr ⟨hc.2.2, S, hS, by
        rw [compress_VU_eq_blockReplace hd, if_pos ⟨hc.1, hc.2.1⟩]⟩
    · rw [if_neg hc]
      refine Or.inl ⟨hS, ?_⟩
      rw [compress_VU_eq_blockReplace hd]
      by_cases hsub : U ⊆ S ∧ Disjoint V S
      · rw [if_pos hsub]
        by_contra hni
        exact hc ⟨hsub.1, hsub.2, hni⟩
      · rw [if_neg hsub]; exact hS
  · rintro (⟨haA, hca⟩ | ⟨haA, b, hb, hcb⟩)
    · refine ⟨a, haA, ?_⟩
      unfold familyUpMap
      by_cases hc : U ⊆ a ∧ Disjoint V a ∧ blockReplace U V a ∉ A
      · exfalso
        rw [compress_VU_eq_blockReplace hd, if_pos ⟨hc.1, hc.2.1⟩] at hca
        exact hc.2.2 hca
      · rw [if_neg hc]
    · refine ⟨b, hb, ?_⟩
      unfold familyUpMap
      rw [compress_VU_eq_blockReplace hd] at hcb
      by_cases hsub : U ⊆ b ∧ Disjoint V b
      · rw [if_pos hsub] at hcb
        subst hcb
        rw [if_pos ⟨hsub.1, hsub.2, haA⟩]
      · rw [if_neg hsub] at hcb
        subst hcb
        exact absurd hb haA
end BooleanIsoperimetry
