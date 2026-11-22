-- Prove2me | solution 1 for BooleanIsoperimetry.downFixed_downClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:24.319084+00:00
-- url     : https://prove2.me/submissions/0c1c3934-3c10-40ff-ae90-57cf2414ba40

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
public import Theorems.Thm_BooleanIsoperimetry_downFixed_sdiff_mem
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
theorem _root_.solution {N : ℕ} {A : Finset (Cube N)}
    (hdown : IsCoordinateDownFixed A) {R S : Cube N} (hS : S ∈ A) (hRS : R ⊆ S) :
    R ∈ A := by
  have h := downFixed_sdiff_mem hdown hS (show S \ R ⊆ S from Finset.sdiff_subset)
  have hrw : S \ (S \ R) = R := by
    ext a
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨haS, h2⟩; by_contra hc; exact h2 ⟨haS, hc⟩
    · intro haR; exact ⟨hRS haR, fun h2 => h2.2 haR⟩
  rwa [hrw] at h
end BooleanIsoperimetry
