-- Prove2me | solution 1 for BooleanIsoperimetry.downFixed_familyUp_erase_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:08.715561+00:00
-- url     : https://prove2.me/submissions/59c2efb0-75fd-48d1-aeef-f756737d2f47

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
    (hdown : IsCoordinateDownFixed A) (W : Cube N) :
    familyUp W ∅ A = A := by
  classical
  have hmap : ∀ S ∈ A, familyUpMap W ∅ A S = S := by
    intro S hS
    unfold familyUpMap
    by_cases hc : W ⊆ S ∧ Disjoint (∅ : Cube N) S ∧ blockReplace W ∅ S ∉ A
    · exfalso
      have hbr : blockReplace W ∅ S = S \ W := by
        unfold blockReplace; simp
      rw [hbr] at hc
      exact hc.2.2 (downFixed_sdiff_mem hdown hS hc.1)
    · rw [if_neg hc]
  unfold familyUp
  rw [Finset.image_congr (g := id) (fun S hS => hmap S hS), Finset.image_id]
end BooleanIsoperimetry
