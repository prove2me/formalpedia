-- Prove2me | solution 1 for FamousTheorems.irrational_rotation_dense_orbit_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:55:20.12369+00:00
-- url     : https://prove2.me/submissions/79fd35d6-ce9f-43a5-bb95-22ac23f535f3

import Mathlib

theorem solution {a p : ℝ} : (DenseRange fun n : ℤ => n • (a : AddCircle p)) ↔ Irrational (a / p) :=
  AddCircle.denseRange_zsmul_coe_iff
