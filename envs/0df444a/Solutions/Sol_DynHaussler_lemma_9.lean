-- Prove2me | solution 1 for DynHaussler.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:05:36.66761+00:00
-- url     : https://prove2.me/submissions/a5e625c9-58c1-434a-8ab0-dcd88dbe6291

import Mathlib
import Definitions.Def_NondualOpt_sfat

set_option autoImplicit false

theorem solution {X : Type*} [Nonempty X] (F : Set (X → ℝ)) (hF : F.Nonempty)
    (hF01 : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (η : ℝ) (hη : 0 < η) :
    ∃ H ⊆ F, H.Nonempty ∧
      (∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → ∃ x, η < |h x - h' x|) ∧
      (∀ f ∈ F, ∃ h ∈ H, ∀ x, |f x - h x| ≤ η) ∧
      NondualOpt.sfat H η ≤ NondualOpt.sfat F η := by
  classical
  obtain ⟨f0, hf0⟩ := hF
  let S : Set (Set (X → ℝ)) :=
    {H | H ⊆ F ∧ ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → ∃ x, η < |h x - h' x|}
  have hS0 : ({f0} : Set (X → ℝ)) ∈ S := by
    refine ⟨Set.singleton_subset_iff.mpr hf0, ?_⟩
    intro h hh h' hh' hne
    rw [Set.mem_singleton_iff] at hh hh'
    exact absurd (hh.trans hh'.symm) hne
  obtain ⟨H, hfH, hmax⟩ := zorn_subset_nonempty S (fun c hcS hc _ => by
    refine ⟨⋃₀ c, ⟨Set.sUnion_subset (fun s hs => (hcS hs).1), ?_⟩,
      fun s hs => Set.subset_sUnion_of_mem hs⟩
    intro h hh h' hh' hne
    obtain ⟨s, hs, hhs⟩ := Set.mem_sUnion.mp hh
    obtain ⟨s', hs', hhs'⟩ := Set.mem_sUnion.mp hh'
    rcases hc.total hs hs' with hss | hss
    · exact (hcS hs').2 h (hss hhs) h' hhs' hne
    · exact (hcS hs).2 h hhs h' (hss hhs') hne) {f0} hS0
  obtain ⟨hHF, hsep⟩ := hmax.1
  refine ⟨H, hHF, ⟨f0, hfH rfl⟩, hsep, ?_, ?_⟩
  · intro f hf
    by_contra hcon
    push_neg at hcon
    have hfH' : f ∉ H := by
      intro hmem
      obtain ⟨x, hx⟩ := hcon f hmem
      rw [sub_self, abs_zero] at hx
      linarith
    have hins : insert f H ∈ S := by
      refine ⟨Set.insert_subset hf hHF, ?_⟩
      intro h hh h' hh' hne
      rcases hh with rfl | hh <;> rcases hh' with rfl | hh'
      · exact absurd rfl hne
      · obtain ⟨x, hx⟩ := hcon h' hh'
        exact ⟨x, hx⟩
      · obtain ⟨x, hx⟩ := hcon h hh
        exact ⟨x, by rw [abs_sub_comm]; exact hx⟩
      · exact hsep h hh h' hh' hne
    have := hmax.2 hins (Set.subset_insert f H)
    exact hfH' (this (Set.mem_insert f H))
  · unfold NondualOpt.sfat
    refine iSup₂_le (fun n hn => ?_)
    obtain ⟨z, s, hzs⟩ := hn
    refine le_iSup₂_of_le n ⟨z, s, fun ε => ?_⟩ (le_refl _)
    obtain ⟨h, hh, ht⟩ := hzs ε
    exact ⟨h, hHF hh, ht⟩
