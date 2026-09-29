-- Prove2me | solution 1 for FamousTheorems.ax_grothendieck
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:22:38.688369+00:00
-- url     : https://prove2.me/submissions/d160e6e4-8bb4-4264-8102-2d531939eade

import Mathlib

theorem solution {K ι : Type*} [Field K] [IsAlgClosed K] [Finite ι] (p : ι → MvPolynomial ι K)
    (hinj : Function.Injective fun (v : ι → K) (i : ι) => MvPolynomial.eval v (p i)) :
    Function.Surjective fun (v : ι → K) (i : ι) => MvPolynomial.eval v (p i) :=
  ax_grothendieck_univ p hinj
