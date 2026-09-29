-- Prove2me | solution 1 for FamousTheorems.p_group_center_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:02:26.326977+00:00
-- url     : https://prove2.me/submissions/40607518-e15d-462e-94a8-93722323377f

import Mathlib

theorem solution {p : ℕ} {G : Type*} [Group G] (hG : IsPGroup p G) [Fact p.Prime] [Nontrivial G] [Finite G] :
    Nontrivial (Subgroup.center G) :=
  hG.center_nontrivial
