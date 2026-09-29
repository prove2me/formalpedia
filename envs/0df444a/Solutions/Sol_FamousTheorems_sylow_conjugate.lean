-- Prove2me | solution 1 for FamousTheorems.sylow_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:33:47.436828+00:00
-- url     : https://prove2.me/submissions/71d8e358-47a1-42f3-bdf4-ea851a360689

import Mathlib

theorem solution {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P Q : Sylow p G) :
    ∃ g : G, g • P = Q :=
  MulAction.exists_smul_eq G P Q
