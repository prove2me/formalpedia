-- Prove2me | solution 1 for DegreeSequences.hh_forward_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:42:56.637833+00:00
-- url     : https://prove2.me/submissions/1f5ce22a-81f1-4f47-ad8b-0631f97a6869

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
public import Theorems.Thm_DegreeSequences_exists_switch
public import Theorems.Thm_DegreeSequences_mem_hhSet
public import Theorems.Thm_DegreeSequences_card_hhSet

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {m : ℕ} (d : Fin (m + 1) → ℕ) (hd : Antitone d) (h0 : d 0 ≤ m) (r : ℕ) :
    ∀ (G : SimpleGraph (Fin (m + 1))) (_ : DecidableRel G.Adj), (∀ i, G.degree i = d i) →
      #{v ∈ hhSet d | ¬ G.Adj 0 v} ≤ r →
      ∃ (G' : SimpleGraph (Fin (m + 1))) (_ : DecidableRel G'.Adj),
        (∀ i, G'.degree i = d i) ∧ ∀ v ∈ hhSet d, G'.Adj 0 v := by
  induction r with
  | zero =>
    intro G _ hG hr
    refine ⟨G, inferInstance, hG, fun v hv => ?_⟩
    by_contra h
    have : v ∈ ({v ∈ hhSet d | ¬ G.Adj 0 v} : Finset _) := mem_filter.mpr ⟨hv, h⟩
    have := card_pos.mpr ⟨v, this⟩
    omega
  | succ r ih =>
    intro G _ hG hr
    by_cases hall : ∀ v ∈ hhSet d, G.Adj 0 v
    · exact ⟨G, inferInstance, hG, hall⟩
    push Not at hall
    obtain ⟨i, hiA, hi⟩ := hall
    have hiA' := (mem_hhSet d i).mp hiA
    obtain ⟨k, hk, hkA⟩ : ∃ k, G.Adj 0 k ∧ k ∉ hhSet d := by
      by_contra hc
      push Not at hc
      have hsub : G.neighborFinset 0 ⊆ (hhSet d).erase i := by
        intro v hv
        rw [mem_neighborFinset] at hv
        exact mem_erase.mpr ⟨fun e => hi (e ▸ hv), hc v hv⟩
      have := card_le_card hsub
      rw [card_neighborFinset_eq_degree, hG, card_erase_of_mem hiA, card_hhSet d h0] at this
      have : i.val ≠ 0 := fun e => hiA'.1 (Fin.ext e)
      omega
    have hik : i ≤ k := by
      rw [mem_hhSet] at hkA
      have hk0 : k ≠ 0 := fun e => G.loopless.irrefl 0 (e ▸ hk)
      rw [Fin.le_iff_val_le_val]
      have := not_and.mp hkA hk0
      omega
    obtain ⟨G', _, hdeg, hadj⟩ := exists_switch G 0 i k (Ne.symm hiA'.1)
      (by rw [hG, hG]; exact hd hik) hi hk
    refine ih G' inferInstance (fun v => (hdeg v).trans (hG v)) ?_
    have hsub : ({v ∈ hhSet d | ¬ G'.Adj 0 v} : Finset _) ⊆
        ({v ∈ hhSet d | ¬ G.Adj 0 v} : Finset _).erase i := by
      intro v hv
      rw [mem_filter, hadj] at hv
      rw [mem_erase, mem_filter]
      refine ⟨fun e => hv.2 (Or.inr e), hv.1, fun h => hv.2 (Or.inl ⟨?_, h⟩)⟩
      rintro rfl
      exact hkA hv.1
    have h1 := card_le_card hsub
    rw [card_erase_of_mem (mem_filter.mpr ⟨hiA, hi⟩)] at h1
    omega
end DegreeSequences
