-- Prove2me | solution 1 for FamousTheorems.cohen_noetherian_prime_ideals_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:56:55.395466+00:00
-- url     : https://prove2.me/submissions/d2052655-d061-4350-98ac-58c9e14a60d2

import Mathlib

theorem solution {R : Type*} [CommRing R] (h : ∀ I : Ideal R, I.IsPrime → I.FG) : IsNoetherianRing R :=
  IsNoetherianRing.of_prime h
