-- Prove2me | solution 1 for CogCons.cognitiveClosure_of_cwo
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:11:24.128144+00:00
-- url     : https://prove2.me/submissions/9edaf327-cc3f-403d-b42c-6609aa9f013b

import Definitions.Def_CogCons_consequence_space

open CogCons CogCons.CognitiveConsequenceSpace

theorem closure_eq_consequence {C : Type*} (S : CognitiveConsequenceSpace C) (A : Set C) :
    S.cognitiveClosure A = S.Cn A := by
  apply Set.Subset.antisymm
  · intro x hx
    exact Set.mem_sInter.mp hx (S.Cn A) ⟨S.Cn_idem A, S.subset_Cn A⟩
  · intro x hx
    apply Set.mem_sInter.mpr
    intro B hB
    have hb := S.Cn_mono A B hB.2 hx
    rw [hB.1] at hb
    exact hb

theorem solution {C : Type*} (S : CognitiveConsequenceSpace C) (A : Set C)
    (hA : S.IsCWO A) :
    S.cognitiveClosure A ≠ A ∧ S.cognitiveClosure Aᶜ = Aᶜ := by
  have hc : S.Cn Aᶜ = Aᶜ := hA
  simp only [closure_eq_consequence]
  refine ⟨?_, hc⟩
  intro ha
  obtain ⟨x, hx⟩ := S.Cn_empty_nonempty
  have hxA := S.Cn_mono ∅ A (Set.empty_subset _) hx
  have hxAc := S.Cn_mono ∅ Aᶜ (Set.empty_subset _) hx
  rw [ha] at hxA
  rw [hc] at hxAc
  exact hxAc hxA
