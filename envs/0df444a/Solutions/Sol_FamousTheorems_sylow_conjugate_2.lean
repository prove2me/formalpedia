-- Prove2me | solution 2 for FamousTheorems.sylow_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:34:31.013229+00:00
-- url     : https://prove2.me/submissions/e34b1045-c3bd-4d12-87f2-45ccb9f716dc

import Mathlib

theorem solution {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P Q : Sylow p G) :
    ∃ g : G, g • P = Q :=
  MulAction.exists_smul_eq G P Q
