-- Prove2me | solution 1 for FamousTheorems.fuglede_putnam_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:52:10.444352+00:00
-- url     : https://prove2.me/submissions/26e04307-8b43-44ac-9781-08ede3ba6550

import Mathlib

theorem solution {A : Type*} [NonUnitalCStarAlgebra A] {a b x : A} (ha : IsStarNormal a) (hb : IsStarNormal b)
    (h : SemiconjBy x a b) :
    SemiconjBy x (star a) (star b) :=
  SemiconjBy.star_right ha hb h
