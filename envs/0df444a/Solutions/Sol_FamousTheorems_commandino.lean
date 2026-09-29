-- Prove2me | solution 1 for FamousTheorems.commandino
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:18:12.926861+00:00
-- url     : https://prove2.me/submissions/59f44210-161f-4e8e-bff8-1debfe964700

import Mathlib

theorem solution {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P] {n : ℕ} [NeZero n]
    [CharZero k] (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.points i -ᵥ s.centroid = (n : k) • (s.centroid -ᵥ s.faceOppositeCentroid i) :=
  s.point_vsub_centroid_eq_smul_vsub i
