-- Prove2me | solution 1 for BookProof.ChapterH9.compress_re_inner_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:33:06.155996+00:00
-- url     : https://prove2.me/submissions/d846f060-1380-4217-af91-7df475162c91

import Definitions.Def_ChapterH4

open BookProof.ChapterH4 ContinuousLinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem solution (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) {a b : ℝ}
    (hlow : ∀ x : E, ‖x‖ = 1 → a ≤ (inner ℂ x (X x) : ℂ).re)
    (hhigh : ∀ x : E, ‖x‖ = 1 → (inner ℂ x (X x) : ℂ).re ≤ b)
    (y : F) (hy : ‖y‖ = 1) :
    a ≤ (inner ℂ y (compress V X y) : ℂ).re
      ∧ (inner ℂ y (compress V X y) : ℂ).re ≤ b := by
  have hVy : ‖V y‖ = 1 := (hViso y).trans hy
  simpa only [compress, comp_apply, adjoint_inner_right] using
    And.intro (hlow (V y) hVy) (hhigh (V y) hVy)

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solution
