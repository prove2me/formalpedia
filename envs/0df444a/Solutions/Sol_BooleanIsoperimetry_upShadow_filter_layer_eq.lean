-- Prove2me | solution 1 for BooleanIsoperimetry.upShadow_filter_layer_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:20:39.469869+00:00
-- url     : https://prove2.me/submissions/a44e3fed-3e12-4214-bf99-7331434361bb

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
    (Finset.upShadow A).filter (fun x => x.card = k) =
      (Finset.upShadow (A.filter (fun x => x.card = k - 1))).filter
        (fun x => x.card = k) := by
  ext x
  constructor
  · intro hx
    rw [Finset.mem_filter] at hx ⊢
    rcases hx with ⟨hxup, hxcard⟩
    rw [Finset.mem_upShadow_iff_exists_sdiff] at hxup ⊢
    rcases hxup with ⟨s, hsA, hsx, hsdiff⟩
    have hscard : s.card = k - 1 := by
      have hcard_sdiff : (x \ s).card = x.card - s.card := Finset.card_sdiff_of_subset hsx
      rw [hcard_sdiff, hxcard] at hsdiff
      have hsle : s.card ≤ k := by
        rw [← hxcard]
        exact Finset.card_le_card hsx
      omega
    exact ⟨⟨s, by simp [hsA, hscard], hsx, hsdiff⟩, hxcard⟩
  · intro hx
    rw [Finset.mem_filter] at hx ⊢
    rcases hx with ⟨hxup, hxcard⟩
    rw [Finset.mem_upShadow_iff_exists_sdiff] at hxup ⊢
    rcases hxup with ⟨s, hsA, hsx, hsdiff⟩
    exact ⟨⟨s, (Finset.mem_filter.mp hsA).1, hsx, hsdiff⟩, hxcard⟩
end BooleanIsoperimetry
