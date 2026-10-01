-- Prove2me | solution 1 for CogCons.Cn_eq_cognitiveClosure
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T20:01:15.044988+00:00
-- url     : https://prove2.me/submissions/3d25d60b-b963-4acb-92bb-ab6c39269945

import Definitions.Def_CogCons_consequence_space

open CogCons CogCons.CognitiveConsequenceSpace

theorem solution {C : Type*} (S : CognitiveConsequenceSpace C) (A : Set C) :
    S.Cn A = S.cognitiveClosure A := by
  apply Set.Subset.antisymm
  · intro x hx
    apply Set.mem_sInter.mpr
    intro D hD
    have h := S.Cn_mono A D hD.2 hx
    rw [hD.1] at h
    exact h
  · intro x hx
    exact Set.mem_sInter.mp hx (S.Cn A) ⟨S.Cn_idem A, S.subset_Cn A⟩
