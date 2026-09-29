-- Prove2me | solution 1 for FamousTheorems.ruzsa_triangle_inequality
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:57:42.166483+00:00
-- url     : https://prove2.me/submissions/71c6fbd3-2eeb-4d04-b86b-9b6ea77dbb01

import Mathlib

open scoped Pointwise

theorem solution {G : Type*} [AddGroup G] [DecidableEq G] (A B C : Finset G) :
    (A - C).card * B.card ≤ (A - B).card * (C - B).card :=
  Finset.ruzsa_triangle_inequality_sub_sub_sub A B C
