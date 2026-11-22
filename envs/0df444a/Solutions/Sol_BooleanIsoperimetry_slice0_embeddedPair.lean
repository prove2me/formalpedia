-- Prove2me | solution 1 for BooleanIsoperimetry.slice0_embeddedPair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:17.779928+00:00
-- url     : https://prove2.me/submissions/91365158-578d-49f9-8182-a6ed21ec7233

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
public import Theorems.Thm_BooleanIsoperimetry_compression_embed0_injective
public import Theorems.Thm_BooleanIsoperimetry_compression_last_not_mem_embed0
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
theorem _root_.solution {N : ℕ} (A B : Finset (Cube N)) :
    slice0 (embeddedPair N A B) = A := by
  ext x
  simp only [slice0, embeddedPair, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨y, hy, hxy⟩ | ⟨y, _hy, hxy⟩)
    · have hyx : y = x := compression_embed0_injective hxy
      simpa [← hyx] using hy
    · have hlast : Fin.last N ∈ embed1 y := by simp [embed1]
      rw [hxy] at hlast
      exact (compression_last_not_mem_embed0 x hlast).elim
  · intro hx
    exact Or.inl ⟨x, hx, rfl⟩
end BooleanIsoperimetry
