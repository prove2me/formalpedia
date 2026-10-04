-- Prove2me | solution 1 for BookProof.ChapterH9.ritz_mem_numRange
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:36:51.638032+00:00
-- url     : https://prove2.me/submissions/d7ac5e72-9fab-483e-b68f-7884c6e75234

import Definitions.Def_ChapterH9

open BookProof.ChapterH4 BookProof.ChapterH9 ContinuousLinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem solution (V : F →L[ℂ] E) (X : E →L[ℂ] E) (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    {lam : ℂ} {y : F} (hy : ‖y‖ = 1) (heig : compress V X y = lam • y) :
    lam ∈ numRange X := by
  change ∃ x : E, ‖x‖ = 1 ∧ inner ℂ x (X x) = lam
  refine ⟨V y, (hViso y).trans hy, ?_⟩
  calc
    inner ℂ (V y) (X (V y)) = inner ℂ y (compress V X y) := by
      simp only [compress, comp_apply, adjoint_inner_right]
    _ = lam := by
      rw [heig, inner_smul_right, inner_self_eq_norm_sq_to_K, hy]
      simp

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solution
