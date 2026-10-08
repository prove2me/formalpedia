-- Prove2me | solution 1 for BeckTeboulleMD.EMDA.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T21:02:50.229515+00:00
-- url     : https://prove2.me/submissions/4c45ab4e-4eb1-4f0b-a297-bfcff73f1073

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

set_option autoImplicit false

open BeckTeboulleMD.EMDA in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (hS : IsOpen S) (ψ : E → ℝ) (hψ : ContDiffOn ℝ 1 ψ S)
    (a b c : E) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ closure S) :
    bregman ψ c a + bregman ψ a b - bregman ψ c b
      = (fderiv ℝ ψ b - fderiv ℝ ψ a) (c - a) := by
  unfold bregman
  have h : c - b = (c - a) + (a - b) := by abel
  rw [h, map_add, ContinuousLinearMap.sub_apply]
  ring

#print axioms solution
