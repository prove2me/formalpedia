-- Prove2me | solution 1 for CogCons.cognitiveClosure_isLeast
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T20:01:24.779517+00:00
-- url     : https://prove2.me/submissions/f80d5a1e-ad72-4376-8cf7-5e02d044cd1f

import Definitions.Def_CogCons_consequence_space

open CogCons CogCons.CognitiveConsequenceSpace

theorem solution {C : Type*} (S : CognitiveConsequenceSpace C) (A : Set C) :
    IsLeast {D : Set C | S.IsDeductive D ∧ A ⊆ D} (S.cognitiveClosure A) := by
  have hEq : S.cognitiveClosure A = S.Cn A := by
    apply Set.Subset.antisymm
    · intro x hx
      exact Set.mem_sInter.mp hx (S.Cn A) ⟨S.Cn_idem A, S.subset_Cn A⟩
    · intro x hx
      apply Set.mem_sInter.mpr
      intro D hD
      have h := S.Cn_mono A D hD.2 hx
      rw [hD.1] at h
      exact h
  rw [hEq]
  refine ⟨⟨S.Cn_idem A, S.subset_Cn A⟩, ?_⟩
  intro D hD x hx
  have h := S.Cn_mono A D hD.2 hx
  rw [hD.1] at h
  exact h
