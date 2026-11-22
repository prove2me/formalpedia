-- Prove2me | solution 1 for FCP.Mersenne.infinitely_many_mersenne_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-22T11:47:28.951432+00:00
-- url     : https://prove2.me/submissions/274ef165-4572-48f1-9e34-953a036f26dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_MersenneLPW_lenstra_pomerance_wagstaff
import Theorems.Thm_MersenneLPW_lpw_implies_infinitude

/-! # Infinitude of Mersenne primes (parent reduction)

Glue: the open child `MersenneLPW.lenstra_pomerance_wagstaff` carries the
Lenstra–Pomerance–Wagstaff asymptotic $C(y) \sim e^{\gamma}\log_2 y$ for the
Mersenne exponent counting function — strictly stronger than infinitude; the
already-Proved bridge `MersenneLPW.lpw_implies_infinitude` (garyholm) extracts
infinitude from that asymptotic. -/

theorem solution : {p : ℕ | (mersenne p).Prime}.Infinite :=
  MersenneLPW.lpw_implies_infinitude MersenneLPW.lenstra_pomerance_wagstaff
