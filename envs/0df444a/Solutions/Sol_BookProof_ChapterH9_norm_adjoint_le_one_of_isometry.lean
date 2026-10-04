-- Prove2me | solution 1 for BookProof.ChapterH9.norm_adjoint_le_one_of_isometry
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T00:49:53.829344+00:00
-- url     : https://prove2.me/submissions/f2537734-30e6-49d9-b9a9-00aaf3c8c09c

import Mathlib.Analysis.InnerProductSpace.Adjoint

/- The target is BookProof.ChapterH9.norm_adjoint_le_one_of_isometry, from
https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean.
The argument uses the isometric adjoint map and the standard operator-norm bound. -/
open ContinuousLinearMap

theorem solution {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V : F →L[ℂ] E) (hViso : ∀ x : F, ‖V x‖ = ‖x‖) : ‖adjoint V‖ ≤ 1 := by
  rw [LinearIsometryEquiv.norm_map adjoint V]
  exact V.opNorm_le_bound zero_le_one fun x ↦ by simp only [hViso x, one_mul, le_refl]

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
