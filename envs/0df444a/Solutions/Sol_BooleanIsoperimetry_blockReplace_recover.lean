-- Prove2me | solution 1 for BooleanIsoperimetry.blockReplace_recover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:24:30.574898+00:00
-- url     : https://prove2.me/submissions/b30172bd-1277-4f92-a036-08b49c5f2fa6

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
theorem _root_.solution {N : ℕ} {U V S : Cube N}
    (hUS : U ⊆ S) (hVS : Disjoint V S) :
    (blockReplace U V S \ V) ∪ U = S := by
  unfold blockReplace
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (⟨hx, hxV⟩ | hxU)
    · rcases hx with ⟨hxS, _⟩ | hxV'
      · exact hxS
      · exact (hxV hxV').elim
    · exact hUS hxU
  · intro hxS
    by_cases hxU : x ∈ U
    · exact Or.inr hxU
    · refine Or.inl ⟨Or.inl ⟨hxS, hxU⟩, ?_⟩
      exact fun hxV => (Finset.disjoint_left.mp hVS hxV hxS)
end BooleanIsoperimetry
