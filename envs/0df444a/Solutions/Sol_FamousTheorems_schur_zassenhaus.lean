-- Prove2me | solution 1 for FamousTheorems.schur_zassenhaus
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:14:41.223086+00:00
-- url     : https://prove2.me/submissions/39b81383-09be-49ac-a0ce-a8b0866a3861

import Mathlib

theorem solution {G : Type*} [Group G] {N : Subgroup G} [N.Normal] (hN : (Nat.card N).Coprime N.index) :
    ∃ H : Subgroup G, H.IsComplement' N :=
  Subgroup.exists_left_complement'_of_coprime hN
