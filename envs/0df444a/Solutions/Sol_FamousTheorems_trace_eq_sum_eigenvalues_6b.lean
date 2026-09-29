-- Prove2me | solution 1 for FamousTheorems.trace_eq_sum_eigenvalues_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:17:46.323119+00:00
-- url     : https://prove2.me/submissions/ecdf41c5-0eed-4e5d-af3f-57f043aeaba8

import Mathlib

theorem solution {n K : Type*} [Fintype n] [DecidableEq n] [Field K] [IsAlgClosed K] (A : Matrix n n K) :
    A.trace = A.charpoly.roots.sum :=
  A.trace_eq_sum_roots_charpoly
