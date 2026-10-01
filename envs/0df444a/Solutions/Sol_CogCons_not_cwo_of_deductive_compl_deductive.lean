-- Prove2me | solution 1 for CogCons.not_cwo_of_deductive_compl_deductive
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:10:53.120908+00:00
-- url     : https://prove2.me/submissions/85eab7b0-77da-4f81-bcd5-2bd831a61d31

import Definitions.Def_CogCons_consequence_space

open CogCons CogCons.CognitiveConsequenceSpace

theorem solution {C : Type*} (S : CognitiveConsequenceSpace C)
    (A : Set C) (hA : S.IsDeductive A) (hAc : S.IsDeductive Aᶜ) :
    ¬ S.IsCWO A := by
  obtain ⟨x, hx⟩ := S.Cn_empty_nonempty
  have hxA := S.Cn_mono ∅ A (Set.empty_subset _) hx
  have hxAc := S.Cn_mono ∅ Aᶜ (Set.empty_subset _) hx
  rw [hA] at hxA
  rw [hAc] at hxAc
  exact False.elim (hxAc hxA)
