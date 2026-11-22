-- Prove2me | solution 1 for BooleanIsoperimetry.slice1_embeddedPair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:23.710413+00:00
-- url     : https://prove2.me/submissions/a0807885-c145-4433-9b6e-7cc161c83330

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
public import Theorems.Thm_BooleanIsoperimetry_compression_last_not_mem_embed0
public import Theorems.Thm_BooleanIsoperimetry_compression_embed1_injective
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
    slice1 (embeddedPair N A B) = B := by
  ext x
  simp only [slice1, embeddedPair, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨y, _hy, hxy⟩ | ⟨y, hy, hxy⟩)
    · have hlast : Fin.last N ∈ embed1 x := by simp [embed1]
      rw [← hxy] at hlast
      exact (compression_last_not_mem_embed0 y hlast).elim
    · have hyx : y = x := compression_embed1_injective hxy
      simpa [← hyx] using hy
  · intro hx
    exact Or.inr ⟨x, hx, rfl⟩
end BooleanIsoperimetry
