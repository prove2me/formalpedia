-- Prove2me | solution 1 for DataValidation.claim_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:09:47.094268+00:00
-- url     : https://prove2.me/submissions/d992a2d4-ab9d-44ae-845a-7cc9e9caef17

import Definitions.Def_DataValidation_transReduction

set_option autoImplicit false

open DataValidation in
theorem solution {V : Type*} [DecidableEq V] (E : Finset (V × V)) (hE : DataValidation.IsAcyclic E) (e : V × V)
    (he : e ∈ E) : (DataValidation.transReduction E).erase e ⊆ DataValidation.transReduction (E.erase e) := by
  classical
  intro f hf
  rw [Finset.mem_erase] at hf
  obtain ⟨hfe, hfT⟩ := hf
  unfold DataValidation.transReduction at hfT ⊢
  rw [Finset.mem_filter] at hfT ⊢
  refine ⟨Finset.mem_erase.2 ⟨hfe, hfT.1⟩, fun hp => hfT.2 ?_⟩
  unfold DataValidation.HasPath at hp ⊢
  exact Relation.TransGen.mono (fun a b h => by
    simp only [Finset.mem_erase] at h ⊢
    exact ⟨h.1, h.2.2⟩) _ _ hp
