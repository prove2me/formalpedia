-- Prove2me | solution 1 for BraidsLinksMCG.puncturedPlaneGroup_free_on_standardGen_step
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T22:46:04.916998+00:00
-- url     : https://prove2.me/submissions/4d519551-7797-484b-aa83-f466f44d13d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops
import Theorems.Thm_BraidsLinksMCG_puncturedPlaneGroup_standardGen_lift_injective_step_v1
import Theorems.Thm_BraidsLinksMCG_puncturedPlaneGroup_standardGen_lift_surjective_step_v1

open BraidsLinksMCG

theorem solution (n : ℕ)
    (ih : ∃ e : PuncturedPlaneGroup n ≃* FreeGroup (Fin n),
      ∀ j : Fin n, e (standardGen n j) = FreeGroup.of j) :
    ∃ e : PuncturedPlaneGroup (n + 1) ≃* FreeGroup (Fin (n + 1)),
      ∀ j : Fin (n + 1), e (standardGen (n + 1) j) = FreeGroup.of j := by
  let f : FreeGroup (Fin (n + 1)) →* PuncturedPlaneGroup (n + 1) :=
    FreeGroup.lift (standardGen (n + 1))
  have hf : Function.Bijective f :=
    ⟨puncturedPlaneGroup_standardGen_lift_injective_step_v1 n ih,
      puncturedPlaneGroup_standardGen_lift_surjective_step_v1 n ih⟩
  let F : FreeGroup (Fin (n + 1)) ≃* PuncturedPlaneGroup (n + 1) :=
    MulEquiv.ofBijective f hf
  refine ⟨F.symm, ?_⟩
  intro j
  have hgen : f (FreeGroup.of j) = standardGen (n + 1) j :=
    FreeGroup.lift_apply_of
  rw [← hgen]
  exact F.symm_apply_apply (FreeGroup.of j)
