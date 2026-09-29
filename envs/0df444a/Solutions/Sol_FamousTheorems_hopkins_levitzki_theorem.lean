-- Prove2me | solution 1 for FamousTheorems.hopkins_levitzki_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:44:07.138994+00:00
-- url     : https://prove2.me/submissions/06dd2d41-0049-47ed-8406-32e042207e7e

import Mathlib

theorem solution {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [IsSemiprimaryRing R] :
    IsNoetherian R M ↔ IsArtinian R M :=
  IsSemiprimaryRing.isNoetherian_iff_isArtinian
