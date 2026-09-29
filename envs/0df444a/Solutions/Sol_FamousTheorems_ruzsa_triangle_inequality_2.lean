-- Prove2me | solution 2 for FamousTheorems.ruzsa_triangle_inequality
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:58:13.271808+00:00
-- url     : https://prove2.me/submissions/f8aa73a3-a60f-470c-a5c8-492334c4d3d5

import Mathlib

open scoped Pointwise

theorem solution {G : Type*} [AddGroup G] [DecidableEq G] (A B C : Finset G) :
    (A - C).card * B.card ≤ (A - B).card * (C - B).card :=
  Finset.ruzsa_triangle_inequality_sub_sub_sub A B C
