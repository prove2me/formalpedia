-- Prove2me | solution 1 for FamousTheorems.z_group_metacyclic_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:08:26.871564+00:00
-- url     : https://prove2.me/submissions/c931c3a1-f3c6-44d4-933d-e59b276df461

import Mathlib

theorem solution {G : Type*} [Group G] [Finite G] :
    IsZGroup G ↔ ∃ (N H : Subgroup G) (φ : H →* MulAut N) (_ : G ≃* N ⋊[φ] H),
      IsCyclic H ∧ IsCyclic N ∧ (Nat.card N).Coprime (Nat.card H) :=
  isZGroup_iff_exists_mulEquiv
