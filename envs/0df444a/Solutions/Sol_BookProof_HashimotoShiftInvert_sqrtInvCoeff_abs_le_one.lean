-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.sqrtInvCoeff_abs_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T02:21:08.759871+00:00
-- url     : https://prove2.me/submissions/e56c9c94-c6ce-4814-95bd-bdfa69ae9799

import Definitions.Def_ChapterHashimotoShiftInvert

open BookProof.HashimotoShiftInvert

-- Direct proof from the registered statement using Mathlib.
theorem solution (n : ℕ) : |sqrtInvCoeff n| ≤ 1 := by
  rw [sqrtInvCoeff, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.mpr (invCoeff_le_one n)

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
