-- Prove2me | solution 1 for FamousTheorems.det_eq_prod_eigenvalues_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:17:40.29708+00:00
-- url     : https://prove2.me/submissions/b277cec7-9841-4f35-b552-51e78c0b0055

import Mathlib

theorem solution {n K : Type*} [Fintype n] [DecidableEq n] [Field K] [IsAlgClosed K] (A : Matrix n n K) :
    A.det = A.charpoly.roots.prod :=
  A.det_eq_prod_roots_charpoly
