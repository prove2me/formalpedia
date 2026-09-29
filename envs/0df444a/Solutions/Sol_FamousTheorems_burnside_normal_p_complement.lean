-- Prove2me | solution 1 for FamousTheorems.burnside_normal_p_complement
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:01:54.805129+00:00
-- url     : https://prove2.me/submissions/6a1cff23-6f42-4dc3-8918-dd8ff8e59784

import Mathlib

theorem solution {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (hP : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ Subgroup.centralizer ((P : Subgroup G) : Set G))
    [(P : Subgroup G).FiniteIndex] : ∃ N : Subgroup G, N.Normal ∧ N.IsComplement' (P : Subgroup G) :=
  ⟨_, inferInstance, MonoidHom.ker_transferSylow_isComplement' P hP⟩
