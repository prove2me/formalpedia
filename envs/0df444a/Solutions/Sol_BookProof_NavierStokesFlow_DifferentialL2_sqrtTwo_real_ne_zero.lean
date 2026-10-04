-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.sqrtTwo_real_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T02:12:03.066677+00:00
-- url     : https://prove2.me/submissions/cc6bae1e-c206-452b-986c-89714eff2d90

import Mathlib

-- Direct specialization of Mathlib square-root positivity.
theorem solution : Real.sqrt 2 ≠ 0 := by
  exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
