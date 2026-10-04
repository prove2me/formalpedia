-- Prove2me | solution 1 for BookProof.ChapterH9.numRange_compress_subset_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:33:10.449984+00:00
-- url     : https://prove2.me/submissions/e3f5b546-dcf1-4c3b-8526-3b83246c1125

import Definitions.Def_ChapterH9

open BookProof.ChapterH4 BookProof.ChapterH9 ContinuousLinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem solution (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) :
    numRange (compress V X) ⊆ Metric.closedBall (0 : ℂ) ‖X‖ := by
  intro z hz
  change ∃ y : F, ‖y‖ = 1 ∧ inner ℂ y (compress V X y) = z at hz
  rcases hz with ⟨y, hy, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖inner ℂ y ((adjoint V) (X (V y)))‖ ≤ ‖X‖
  rw [adjoint_inner_right]
  have hVy : ‖V y‖ = 1 := (hViso y).trans hy
  calc
    ‖inner ℂ (V y) (X (V y))‖ ≤ ‖V y‖ * ‖X (V y)‖ := norm_inner_le_norm _ _
    _ ≤ ‖V y‖ * (‖X‖ * ‖V y‖) :=
      mul_le_mul_of_nonneg_left (X.le_opNorm (V y)) (norm_nonneg _)
    _ = ‖X‖ := by rw [hVy, one_mul, mul_one]

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solution
