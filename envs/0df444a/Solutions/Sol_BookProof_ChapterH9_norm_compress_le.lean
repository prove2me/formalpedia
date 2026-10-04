-- Prove2me | solution 1 for BookProof.ChapterH9.norm_compress_le
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:03:15.9014+00:00
-- url     : https://prove2.me/submissions/d06be1c3-8101-4a93-a0b4-95eb91105e77

import Definitions.Def_ChapterH4

open BookProof.ChapterH4 ContinuousLinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem solution (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) : ‖compress V X‖ ≤ ‖X‖ := by
  have hV : ‖V‖ ≤ 1 := V.opNorm_le_bound zero_le_one (by simpa only [one_mul] using fun x => (hViso x).le)
  have hVa : ‖adjoint V‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using hV
  change ‖(adjoint V).comp (X.comp V)‖ ≤ ‖X‖
  calc
    _ ≤ ‖adjoint V‖ * ‖X.comp V‖ := (adjoint V).opNorm_comp_le _
    _ ≤ 1 * (‖X‖ * 1) := mul_le_mul hVa
      ((X.opNorm_comp_le V).trans (mul_le_mul_of_nonneg_left hV (norm_nonneg _)))
      (norm_nonneg _) zero_le_one
    _ = ‖X‖ := by simp only [one_mul, mul_one]

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solution
