-- Prove2me | solution 1 for FamousTheorems.ghys_semiconjugacy_circle_actions_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:13:46.935339+00:00
-- url     : https://prove2.me/submissions/6f8791f7-ced2-470d-8b83-25dc3eb8d8cc

import Mathlib

theorem solution {G : Type*} [Group G] (f₁ f₂ : G →* CircleDeg1Lift)
    (h : ∀ g, (f₁ g).translationNumber = (f₂ g).translationNumber) :
    ∃ F : CircleDeg1Lift, ∀ g, Function.Semiconj F (f₁ g) (f₂ g) :=
  CircleDeg1Lift.semiconj_of_group_action_of_forall_translationNumber_eq f₁ f₂ h
