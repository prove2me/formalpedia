-- Prove2me | solution 1 for FamousTheorems.krull_height_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:43:42.022785+00:00
-- url     : https://prove2.me/submissions/af342b49-e657-442b-9fe0-6eb4dc447c33

import Mathlib

theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R] (I p : Ideal R) (hp : p ∈ I.minimalPrimes) :
    p.height ≤ Cardinal.toENat (Submodule.spanRank I) :=
  Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes I p hp
