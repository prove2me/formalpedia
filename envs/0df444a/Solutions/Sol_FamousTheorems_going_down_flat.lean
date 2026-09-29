-- Prove2me | solution 1 for FamousTheorems.going_down_flat
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:15:56.939206+00:00
-- url     : https://prove2.me/submissions/81cb09af-67dc-4940-8b79-c9b6fa7b6d12

import Mathlib

theorem solution {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] {p q : Ideal R} [p.IsPrime]
    [q.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver q] (hpq : p < q) :
    ∃ P < Q, P.IsPrime ∧ P.LiesOver p :=
  Ideal.exists_ideal_lt_liesOver_of_lt Q hpq
