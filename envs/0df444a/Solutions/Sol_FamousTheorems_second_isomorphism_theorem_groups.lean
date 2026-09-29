-- Prove2me | solution 1 for FamousTheorems.second_isomorphism_theorem_groups
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:34:02.744997+00:00
-- url     : https://prove2.me/submissions/4425a7ff-6536-482e-a936-8a01fcf25340

import Mathlib

theorem solution {G : Type*} [Group G] (H N : Subgroup G) [N.Normal] :
    Nonempty (H ⧸ N.subgroupOf H ≃* ↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) :=
  ⟨QuotientGroup.quotientInfEquivProdNormalQuotient H N⟩
