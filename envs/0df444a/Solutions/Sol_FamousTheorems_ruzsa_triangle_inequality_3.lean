-- Prove2me | solution 3 for FamousTheorems.ruzsa_triangle_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T21:59:08.736575+00:00
-- url     : https://prove2.me/submissions/6ee44801-2e46-480a-bee3-9962d040e194

import Mathlib

open scoped Pointwise

theorem solution {G : Type*} [AddGroup G] [DecidableEq G] (A B C : Finset G) :
    (A - C).card * B.card ≤ (A - B).card * (C - B).card := by
  exact Finset.ruzsa_triangle_inequality_sub_sub_sub A B C
