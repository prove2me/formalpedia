-- Prove2me | solution 1 for FamousTheorems.gregory_newton_forward_difference
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:02:36.187584+00:00
-- url     : https://prove2.me/submissions/df176165-e4d2-4ba7-b08f-7ad11dc5f673

import Mathlib

theorem solution {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M) (f : M → G) (n : ℕ) (y : M) :
    f (y + n • h) = ∑ k ∈ Finset.range (n + 1), n.choose k • (fwdDiff h)^[k] f y :=
  shift_eq_sum_fwdDiff_iter h f n y
