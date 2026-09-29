-- Prove2me | solution 1 for FamousTheorems.birkhoff_von_neumann
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:07:08.008204+00:00
-- url     : https://prove2.me/submissions/5615c087-698d-45bf-b994-4b82ef843b1f

import Mathlib

theorem solution {R n : Type*} [Fintype n] [DecidableEq n] [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    (doublyStochastic R n : Set (Matrix n n R)) =
      convexHull R {x : Matrix n n R | ∃ σ : Equiv.Perm n, Equiv.Perm.permMatrix R σ = x} :=
  doublyStochastic_eq_convexHull_permMatrix
