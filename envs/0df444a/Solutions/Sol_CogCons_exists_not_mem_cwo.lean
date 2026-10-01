-- Prove2me | solution 1 for CogCons.exists_not_mem_cwo
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T20:02:55.566332+00:00
-- url     : https://prove2.me/submissions/40c854ae-c95b-4ca5-90b2-eb93c2e65f59

import Definitions.Def_CogCons_consequence_space

open CogCons CogCons.CognitiveConsequenceSpace

theorem solution {C : Type*} (S : CognitiveConsequenceSpace C) :
    ∃ f : C, ∀ A : Set C, S.IsCWO A → f ∉ A := by
  obtain ⟨f, hf⟩ := S.Cn_empty_nonempty
  refine ⟨f, ?_⟩
  intro A hA
  have h : f ∈ S.Cn Aᶜ := S.Cn_mono ∅ Aᶜ (Set.empty_subset _) hf
  change S.Cn Aᶜ = Aᶜ at hA
  rw [hA] at h
  exact h
