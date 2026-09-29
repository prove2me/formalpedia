-- Prove2me | solution 1 for FamousTheorems.akizuki_hopkins_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:45:33.290463+00:00
-- url     : https://prove2.me/submissions/6ee728cf-ff9f-4750-bcff-e2848f0ff6e5

import Mathlib

theorem solution {R : Type*} [CommRing R] : IsArtinianRing R ↔ IsNoetherianRing R ∧ Ring.KrullDimLE 0 R :=
  isArtinianRing_iff_isNoetherianRing_krullDimLE_zero
