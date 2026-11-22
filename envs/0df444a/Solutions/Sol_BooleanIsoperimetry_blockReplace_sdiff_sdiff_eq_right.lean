-- Prove2me | solution 1 for BooleanIsoperimetry.blockReplace_sdiff_sdiff_eq_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:46.476845+00:00
-- url     : https://prove2.me/submissions/479b07c1-c0d1-4445-ab04-8c8c7d036a00

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
theorem _root_.solution {N : ℕ} (S T : Cube N) :
    blockReplace (S \ T) (T \ S) S = T := by
  unfold blockReplace
  ext a
  simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (⟨haS, hnot⟩ | ⟨haT, _⟩)
    · by_contra haT
      exact hnot ⟨haS, haT⟩
    · exact haT
  · intro haT
    by_cases haS : a ∈ S
    · exact Or.inl ⟨haS, fun h => h.2 haT⟩
    · exact Or.inr ⟨haT, haS⟩
end BooleanIsoperimetry
