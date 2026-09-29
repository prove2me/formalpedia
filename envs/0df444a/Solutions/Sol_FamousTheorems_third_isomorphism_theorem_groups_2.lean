-- Prove2me | solution 2 for FamousTheorems.third_isomorphism_theorem_groups
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:31:49.367237+00:00
-- url     : https://prove2.me/submissions/da5f4086-f217-4621-b694-af6c2a52a127

import Mathlib

theorem solution {G : Type*} [Group G] (N M : Subgroup G) [N.Normal] [M.Normal] (h : N ≤ M) :
    Nonempty ((G ⧸ N) ⧸ M.map (QuotientGroup.mk' N) ≃* G ⧸ M) :=
  ⟨QuotientGroup.quotientQuotientEquivQuotient N M h⟩
