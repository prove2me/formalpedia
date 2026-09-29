-- Prove2me | solution 1 for FamousTheorems.real_ring_endomorphism_identity_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:19:00.913524+00:00
-- url     : https://prove2.me/submissions/ef45e356-3d3c-4d61-9e98-1662ddb32121

import Mathlib

theorem solution (f : ℝ →+* ℝ) : f = RingHom.id ℝ :=
  Subsingleton.elim f _
