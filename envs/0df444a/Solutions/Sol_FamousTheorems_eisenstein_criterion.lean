-- Prove2me | solution 1 for FamousTheorems.eisenstein_criterion
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T07:14:54.048273+00:00
-- url     : https://prove2.me/submissions/32565226-194d-43ed-b629-4ae2269f7af4

import Mathlib

universe u v

open Filter Set Topology DirectSum

theorem solution {R : Type*} [CommRing R] [IsDomain R] {f : Polynomial R}
    {P : Ideal R} (hP : P.IsPrime) (hfl : f.leadingCoeff ∉ P)
    (hfP : ∀ n : ℕ, (n : WithBot ℕ) < f.degree → f.coeff n ∈ P) (hfd0 : 0 < f.degree)
    (h0 : f.coeff 0 ∉ P ^ 2) (hu : f.IsPrimitive) : Irreducible f :=
  Polynomial.irreducible_of_eisenstein_criterion hP hfl hfP hfd0 h0 hu
