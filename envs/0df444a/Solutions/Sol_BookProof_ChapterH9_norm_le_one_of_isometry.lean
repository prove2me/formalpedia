-- Prove2me | solution 1 for BookProof.ChapterH9.norm_le_one_of_isometry
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T00:48:58.645932+00:00
-- url     : https://prove2.me/submissions/922dba28-14d2-4096-b35e-a3c873ebc0b3

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/- The target is BookProof.ChapterH9.norm_le_one_of_isometry, from
https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean.
This is the standard Mathlib operator-norm bound, as in the source argument. -/
theorem solution {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (V : F →L[ℂ] E) (hViso : ∀ x : F, ‖V x‖ = ‖x‖) : ‖V‖ ≤ 1 := by
  exact V.opNorm_le_bound zero_le_one fun x ↦ by simp only [hViso x, one_mul, le_refl]

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
