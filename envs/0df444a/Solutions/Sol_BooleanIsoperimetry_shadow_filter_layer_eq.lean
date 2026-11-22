-- Prove2me | solution 1 for BooleanIsoperimetry.shadow_filter_layer_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:09.885862+00:00
-- url     : https://prove2.me/submissions/ea0b5cb0-d13a-41fa-a6e5-eb3fe40eb01f

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
theorem _root_.solution {N : ℕ} (A : Finset (Cube N)) (k : ℕ) :
    (Finset.shadow A).filter (fun x => x.card = k) =
      (Finset.shadow (A.filter (fun x => x.card = k + 1))).filter
        (fun x => x.card = k) := by
  ext x
  constructor
  · intro hx
    rw [Finset.mem_filter] at hx ⊢
    rcases hx with ⟨hxsh, hxcard⟩
    rw [Finset.mem_shadow_iff_exists_sdiff] at hxsh ⊢
    rcases hxsh with ⟨s, hsA, hxs, hsdiff⟩
    have hscard : s.card = k + 1 := by
      have hcard_sdiff : (s \ x).card = s.card - x.card := Finset.card_sdiff_of_subset hxs
      rw [hcard_sdiff, hxcard] at hsdiff
      have hxle : k ≤ s.card := by
        rw [← hxcard]
        exact Finset.card_le_card hxs
      omega
    exact ⟨⟨s, by simp [hsA, hscard], hxs, hsdiff⟩, hxcard⟩
  · intro hx
    rw [Finset.mem_filter] at hx ⊢
    rcases hx with ⟨hxsh, hxcard⟩
    rw [Finset.mem_shadow_iff_exists_sdiff] at hxsh ⊢
    rcases hxsh with ⟨s, hsA, hxs, hsdiff⟩
    exact ⟨⟨s, (Finset.mem_filter.mp hsA).1, hxs, hsdiff⟩, hxcard⟩
end BooleanIsoperimetry
