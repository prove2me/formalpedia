-- Prove2me | solution 1 for BookProof.ChapterH9.convexHull_numRange_compress_mono
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T02:10:12.556639+00:00
-- url     : https://prove2.me/submissions/eb0cbf3d-dd07-450e-ac70-528e0c872866

import Definitions.Def_ChapterH9

open BookProof.ChapterH4 BookProof.ChapterH9 ContinuousLinearMap

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

private theorem compression_range_subset (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hV : ∀ y : F, ‖V y‖ = ‖y‖) : numRange (compress V X) ⊆ numRange X := by
  intro z hz
  change ∃ y : F, ‖y‖ = 1 ∧ inner ℂ y (compress V X y) = z at hz
  rcases hz with ⟨y, hy, hz⟩
  change ∃ x : E, ‖x‖ = 1 ∧ inner ℂ x (X x) = z
  refine ⟨V y, (hV y).trans hy, ?_⟩
  simpa only [compress, comp_apply, adjoint_inner_right] using hz

theorem solution (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E)
    (J : F →L[ℂ] G) (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J)
    (hJiso : ∀ x : F, ‖J x‖ = ‖x‖) :
    convexHull ℝ (numRange (compress Vn X)) ⊆ convexHull ℝ (numRange (compress Vm X)) := by
  apply convexHull_mono
  have hc : compress Vn X = compress J (compress Vm X) := by
    simp only [hJ, compress, adjoint_comp, comp_assoc]
  rw [hc]
  exact compression_range_subset J (compress Vm X) hJiso

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solution
