-- Prove2me | solution 1 for FamousTheorems.transcendence_basis_card_trdeg_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:02:29.319216+00:00
-- url     : https://prove2.me/submissions/ae5dd48a-037a-4b52-b559-80f824e13190

import Mathlib

theorem solution {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial R] [NoZeroDivisors A] {x : ι → A}
    (hx : IsTranscendenceBasis R x) :
    Cardinal.lift.{u_3} (Cardinal.mk ι) = Cardinal.lift.{u_1} (Algebra.trdeg R A) :=
  hx.lift_cardinalMk_eq_trdeg
