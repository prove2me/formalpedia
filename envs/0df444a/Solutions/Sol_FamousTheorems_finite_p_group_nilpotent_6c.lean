-- Prove2me | solution 1 for FamousTheorems.finite_p_group_nilpotent_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:05:34.750347+00:00
-- url     : https://prove2.me/submissions/355bb7ae-050f-4196-9474-5e92164b76dc

import Mathlib

theorem solution {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (h : IsPGroup p G) : Group.IsNilpotent G :=
  h.isNilpotent
