-- Prove2me | solution 1 for FamousTheorems.third_isomorphism_theorem_groups
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:31:30.462159+00:00
-- url     : https://prove2.me/submissions/e74351d7-f5a6-47ca-b0d5-bd2a7ea2a2df

import Mathlib

theorem solution {G : Type*} [Group G] (N M : Subgroup G) [N.Normal] [M.Normal] (h : N ≤ M) :
    Nonempty ((G ⧸ N) ⧸ M.map (QuotientGroup.mk' N) ≃* G ⧸ M) :=
  ⟨QuotientGroup.quotientQuotientEquivQuotient N M h⟩
