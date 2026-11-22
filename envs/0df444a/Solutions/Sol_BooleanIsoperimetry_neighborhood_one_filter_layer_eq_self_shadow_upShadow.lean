-- Prove2me | solution 1 for BooleanIsoperimetry.neighborhood_one_filter_layer_eq_self_shadow_upShadow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:09.925312+00:00
-- url     : https://prove2.me/submissions/467d10ad-51a0-4c96-9a4a-64da904d4a2a

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
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_one_eq_self_union_shadow_upShadow
public import Theorems.Thm_BooleanIsoperimetry_shadow_filter_layer_eq
public import Theorems.Thm_BooleanIsoperimetry_upShadow_filter_layer_eq
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
theorem _root_.solution {N : ℕ}
    (A : Finset (Cube N)) (k : ℕ) :
    (neighborhood 1 A).filter (fun x => x.card = k) =
      (A.filter (fun x => x.card = k)) ∪
        ((Finset.shadow (A.filter (fun x => x.card = k + 1))).filter
          (fun x => x.card = k)) ∪
        ((Finset.upShadow (A.filter (fun x => x.card = k - 1))).filter
          (fun x => x.card = k)) := by
  rw [neighborhood_one_eq_self_union_shadow_upShadow]
  ext x
  have hshadow :
      (x ∈ Finset.shadow A ∧ x.card = k) ↔
        (x ∈ Finset.shadow (A.filter (fun x => x.card = k + 1)) ∧ x.card = k) := by
    have hmem := congrArg (fun S : Finset (Cube N) => x ∈ S) (shadow_filter_layer_eq A k)
    exact Iff.of_eq (by simpa only [Finset.mem_filter] using hmem)
  have hupShadow :
      (x ∈ Finset.upShadow A ∧ x.card = k) ↔
        (x ∈ Finset.upShadow (A.filter (fun x => x.card = k - 1)) ∧ x.card = k) := by
    have hmem := congrArg (fun S : Finset (Cube N) => x ∈ S) (upShadow_filter_layer_eq A k)
    exact Iff.of_eq (by simpa only [Finset.mem_filter] using hmem)
  simp only [Finset.mem_filter, Finset.mem_union]
  tauto
end BooleanIsoperimetry
