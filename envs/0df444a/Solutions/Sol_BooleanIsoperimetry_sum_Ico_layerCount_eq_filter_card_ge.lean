-- Prove2me | solution 1 for BooleanIsoperimetry.sum_Ico_layerCount_eq_filter_card_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:20:13.477467+00:00
-- url     : https://prove2.me/submissions/390d7f8e-10d7-4b91-a1f9-dd367b6e4ad5

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry
open Finset
namespace BooleanIsoperimetry
theorem _root_.solution (N k : ℕ) (A : Finset (Cube N)) :
    ∑ r ∈ Finset.Ico k (N + 2), layerCount N r A
      = (A.filter (fun x => k ≤ x.card)).card := by
  rw [show { x ∈ A | k ≤ #x } =
      Finset.biUnion (Finset.Ico k (N + 2) ) (fun r => Finset.filter (fun x => x.card = r) A)
    from ?_, Finset.card_biUnion]
  · rfl
  · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz hz' => hxy <| by aesop
  · ext x; simp +decide only [mem_filter, mem_biUnion, mem_Ico, exists_eq_right_right']
    exact ⟨ fun h =>
      ⟨ ⟨ h.2, by linarith [show #x ≤ N by simpa using Finset.card_le_univ x] ⟩,
        h.1 ⟩,
      fun h => ⟨ h.2, h.1.1 ⟩ ⟩
end BooleanIsoperimetry
