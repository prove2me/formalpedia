-- Prove2me | solution 1 for FamousTheorems.fundamental_identity_ramification_inertia
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:19:06.111474+00:00
-- url     : https://prove2.me/submissions/f15040ca-c55e-4df8-9161-d5be7a669e1d

import Mathlib

theorem solution {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Module.Finite R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] [Fintype (p.primesOver S)] :
    ∑ q : p.primesOver S, q.1.ramificationIdx R * q.1.inertiaDeg R = Module.finrank R S :=
  Ideal.sum_ramification_inertia_eq_finrank p S
