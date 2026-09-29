-- Prove2me | solution 1 for FamousTheorems.gauss_lemma_polynomials
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:22:30.721207+00:00
-- url     : https://prove2.me/submissions/cd678023-8c5d-45ef-8c62-5d5ac8249d41

import Mathlib

theorem solution {R K : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R] [Field K] [Algebra R K] [IsFractionRing R K]
    {p : Polynomial R} (hp : p.IsPrimitive) :
    Irreducible p ↔ Irreducible (p.map (algebraMap R K)) :=
  hp.irreducible_iff_irreducible_map_fraction_map
