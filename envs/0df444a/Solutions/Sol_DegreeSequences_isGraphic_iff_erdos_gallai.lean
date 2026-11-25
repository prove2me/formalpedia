-- Prove2me | solution 1 for DegreeSequences.isGraphic_iff_erdos_gallai
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:51:44.284256+00:00
-- url     : https://prove2.me/submissions/8203435a-039d-44dd-8c95-b96b494ed6b8

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
public import Theorems.Thm_DegreeSequences_eg_necessary
public import Theorems.Thm_DegreeSequences_eg_sufficient

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {n : ℕ} (d : Fin n → ℕ) (hd : Antitone d) :
    IsGraphic d ↔ Even (∑ i, d i) ∧
      ∀ k ≤ n, ∑ i with i.val < k, d i ≤ k * (k - 1) + ∑ i with k ≤ i.val, min (d i) k := by
  constructor
  · rintro ⟨G, _, hG⟩
    refine ⟨?_, fun k _ => ?_⟩
    · have h := G.sum_degrees_eq_twice_card_edges
      simp only [hG] at h
      rw [h]
      exact even_two_mul _
    · simpa only [hG] using eg_necessary G k
  · rintro ⟨hev, hEG⟩
    exact eg_sufficient _ d rfl hd hev hEG
end DegreeSequences
