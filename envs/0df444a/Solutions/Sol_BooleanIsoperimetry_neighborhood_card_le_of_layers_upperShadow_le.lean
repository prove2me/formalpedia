-- Prove2me | solution 1 for BooleanIsoperimetry.neighborhood_card_le_of_layers_upperShadow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:04.959972+00:00
-- url     : https://prove2.me/submissions/d4b84547-eb9d-43fd-b366-7d6c06412d97

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
public import Theorems.Thm_BooleanIsoperimetry_card_eq_sum_card_filter_layer
public import Theorems.Thm_BooleanIsoperimetry_upShadow_filter_layer_eq
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_one_filter_layer_eq_self_shadow_upShadow
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
theorem _root_.solution {N r : ℕ}
    {A A' : Finset (Cube N)} (hr : 1 ≤ r)
    (hA_le : ∀ w ∈ A, w.card ≤ r) (hA'_le : ∀ w ∈ A', w.card ≤ r)
    (hA_full : ∀ z : Cube N, z.card < r → z ∈ A)
    (hA'_full : ∀ z : Cube N, z.card < r → z ∈ A')
    (h_shadow : (upperLayerShadow N r A').card ≤ (upperLayerShadow N r A).card) :
    (neighborhood 1 A').card ≤ (neighborhood 1 A).card := by
  have hmem_gen : ∀ (B : Finset (Cube N)), (∀ z : Cube N, z.card < r → z ∈ B) →
      ∀ z : Cube N, z.card ≤ r → z ∈ neighborhood 1 B := by
    intro B hBfull z hz
    rw [mem_neighborhood_iff]
    rcases lt_or_eq_of_le hz with hlt | heq
    · exact ⟨z, hBfull z hlt, by unfold hDist; simp⟩
    · have hzne : z.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨a, ha⟩ := hzne
      refine ⟨z.erase a, hBfull _ ?_, ?_⟩
      · rw [Finset.card_erase_of_mem ha]; omega
      · have hsub : symmDiff (z.erase a) z ⊆ {a} := by
          intro w hw
          rw [Finset.mem_symmDiff] at hw
          simp only [Finset.mem_singleton]
          rcases hw with ⟨hwe, hwnz⟩ | ⟨hwz, hwne⟩
          · exact absurd (Finset.mem_of_mem_erase hwe) hwnz
          · by_contra hne
            exact hwne (Finset.mem_erase.mpr ⟨hne, hwz⟩)
        unfold hDist
        calc (symmDiff (z.erase a) z).card ≤ ({a} : Finset (Fin N)).card :=
              Finset.card_le_card hsub
          _ = 1 := Finset.card_singleton a
  have hmemA := hmem_gen A hA_full
  have hmemA' := hmem_gen A' hA'_full
  have nbhd_layer_top : ∀ (B : Finset (Cube N)), (∀ w ∈ B, w.card ≤ r) →
      (neighborhood 1 B).filter (fun z => z.card = r + 1) = upperLayerShadow N r B := by
    intro B hB
    rw [neighborhood_one_filter_layer_eq_self_shadow_upShadow]
    have e1 : B.filter (fun z => z.card = r + 1) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro w hw; have := hB w hw; omega
    have e2 : B.filter (fun z => z.card = r + 1 + 1) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro w hw; have := hB w hw; omega
    simp only [e1, e2, Finset.shadow_empty, Finset.filter_empty, Finset.empty_union]
    rw [← upShadow_filter_layer_eq B (r + 1)]
    rfl
  have nbhd_layer_high : ∀ (B : Finset (Cube N)) (k : ℕ), (∀ w ∈ B, w.card ≤ r) → r + 1 < k →
      (neighborhood 1 B).filter (fun z => z.card = k) = ∅ := by
    intro B k hB hk
    rw [neighborhood_one_filter_layer_eq_self_shadow_upShadow]
    have e0 : B.filter (fun z => z.card = k) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro w hw; have := hB w hw; omega
    have e1 : B.filter (fun z => z.card = k + 1) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro w hw; have := hB w hw; omega
    have e2 : B.filter (fun z => z.card = k - 1) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro w hw; have := hB w hw; omega
    simp only [e0, e1, e2, Finset.shadow_empty, Finset.upShadow_empty, Finset.filter_empty,
        Finset.union_empty]
  have key : ∀ k ∈ Finset.range (N + 1),
      ((neighborhood 1 A').filter (fun z => z.card = k)).card
        ≤ ((neighborhood 1 A).filter (fun z => z.card = k)).card := by
    intro k _
    by_cases hkr : k ≤ r
    · have eqA : (neighborhood 1 A).filter (fun z => z.card = k)
          = Finset.univ.filter (fun z : Cube N => z.card = k) := by
        ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.2, fun hc => ⟨hmemA z (by omega), hc⟩⟩
      have eqA' : (neighborhood 1 A').filter (fun z => z.card = k)
          = Finset.univ.filter (fun z : Cube N => z.card = k) := by
        ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.2, fun hc => ⟨hmemA' z (by omega), hc⟩⟩
      rw [eqA, eqA']
    · have hkr' : r < k := not_le.mp hkr
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hkr') with hk1 | hk2
      · have hkeq : k = r + 1 := hk1.symm
        subst hkeq
        rw [nbhd_layer_top A' hA'_le, nbhd_layer_top A hA_le]
        exact h_shadow
      · rw [nbhd_layer_high A' k hA'_le hk2, nbhd_layer_high A k hA_le hk2]
  rw [card_eq_sum_card_filter_layer (neighborhood 1 A'),
      card_eq_sum_card_filter_layer (neighborhood 1 A)]
  exact Finset.sum_le_sum key
end BooleanIsoperimetry
