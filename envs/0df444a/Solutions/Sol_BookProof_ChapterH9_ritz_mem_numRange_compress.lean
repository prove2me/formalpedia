-- Prove2me | solution 1 for BookProof.ChapterH9.ritz_mem_numRange_compress
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:36:52.95942+00:00
-- url     : https://prove2.me/submissions/4229acc2-720e-4b95-8f6f-787a4015339f

import Definitions.Def_ChapterH9

open BookProof.ChapterH4 BookProof.ChapterH9 ContinuousLinearMap

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem solution (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J) (hJiso : ∀ x : F, ‖J x‖ = ‖x‖)
    {lam : ℂ} {y : F} (hy : ‖y‖ = 1) (heig : compress Vn X y = lam • y) :
    lam ∈ numRange (compress Vm X) := by
  change ∃ x : G, ‖x‖ = 1 ∧ inner ℂ x (compress Vm X x) = lam
  refine ⟨J y, (hJiso y).trans hy, ?_⟩
  calc
    inner ℂ (J y) (compress Vm X (J y)) = inner ℂ y (compress Vn X y) := by
      simp only [hJ, compress, adjoint_comp, comp_apply, adjoint_inner_right]
    _ = lam := by
      rw [heig, inner_smul_right, inner_self_eq_norm_sq_to_K, hy]
      simp

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solution
