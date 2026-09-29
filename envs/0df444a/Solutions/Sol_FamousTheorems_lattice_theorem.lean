-- Prove2me | solution 1 for FamousTheorems.lattice_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:17:50.944725+00:00
-- url     : https://prove2.me/submissions/eeec3041-0746-4146-9acb-a7939f206d57

import Mathlib

theorem solution {G : Type*} [Group G] (N : Subgroup G) [N.Normal] :
    ∃ e : Subgroup (G ⧸ N) ≃o {H : Subgroup G // N ≤ H},
      ∀ K : Subgroup (G ⧸ N), (e K : Subgroup G) = Subgroup.comap (QuotientGroup.mk' N) K :=
  ⟨QuotientGroup.comapMk'OrderIso N, fun _ => rfl⟩
