-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.sqrtTwo_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T02:12:04.552282+00:00
-- url     : https://prove2.me/submissions/eb0b8d36-a11e-4f61-b711-78989ce109be

import Mathlib

-- Direct specialization of Mathlib positivity and the injective real-to-complex cast.
theorem solution : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num)) : Real.sqrt 2 ≠ 0)

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
