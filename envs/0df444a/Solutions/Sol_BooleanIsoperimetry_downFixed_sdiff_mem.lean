-- Prove2me | solution 1 for BooleanIsoperimetry.downFixed_sdiff_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:18.157079+00:00
-- url     : https://prove2.me/submissions/5c2a435c-ff97-4f54-8e80-72158ec258ec

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
public import Theorems.Thm_BooleanIsoperimetry_downFixed_erase_mem
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
    (hdown : IsCoordinateDownFixed A) {S W : Cube N} (hS : S ∈ A) (hWS : W ⊆ S) :
    S \ W ∈ A := by
  classical
  induction W using Finset.induction generalizing S with
  | empty => simpa using hS
  | @insert i W hiW ih =>
      have hiS : i ∈ S := hWS (Finset.mem_insert_self i W)
      have hWsub : W ⊆ S := fun a ha => hWS (Finset.mem_insert_of_mem ha)
      have hSi : S.erase i ∈ A := downFixed_erase_mem hdown hS hiS
      have hWsubErase : W ⊆ S.erase i := by
        intro a ha
        rw [Finset.mem_erase]
        exact ⟨fun hai => hiW (hai ▸ ha), hWsub ha⟩
      have := ih hSi hWsubErase
      have hrw : (S.erase i) \ W = S \ insert i W := by
        ext a
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
        tauto
      rwa [hrw] at this
end BooleanIsoperimetry
