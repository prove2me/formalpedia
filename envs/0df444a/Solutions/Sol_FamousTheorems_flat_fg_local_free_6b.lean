-- Prove2me | solution 1 for FamousTheorems.flat_fg_local_free_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:07:42.39598+00:00
-- url     : https://prove2.me/submissions/84530ac0-a269-4f83-8a94-e52829c7fc91

import Mathlib

theorem solution {R P : Type*} [CommRing R] [AddCommGroup P] [Module R P] [IsLocalRing R] [Module.Finite R P]
    [Module.Flat R P] : Module.Free R P :=
  Module.free_of_flat_of_isLocalRing
