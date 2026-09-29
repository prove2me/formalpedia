-- Prove2me | solution 1 for BookProof.FriedrichsFormGap.formSpace_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:17:52.86827+00:00
-- url     : https://prove2.me/submissions/e77f41ce-f42d-47b5-a1e8-e7b507ae3648

-- Adapted from Leonardo Pedro, timepiece commit61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFriedrichsFormGap.lean
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
set_option autoImplicit false
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

private theorem formExt_coe (P : PosSymOp F) (x : FormDom P) :
    formExt P (x : FormSpace P) = toAmbient x := by
  have hi : IsUniformInducing (UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := FormDom P)) := by
    simpa [UniformSpace.Completion.coe_toComplL] using
      UniformSpace.Completion.isUniformInducing_coe (FormDom P)
  have := ContinuousLinearMap.extend_eq (incl P) (denseRange_toComplL P) hi x
  simpa [formExt, incl, inclLin, UniformSpace.Completion.coe_toComplL] using this

theorem solution (P : PosSymOp F) {mu : ℝ}
    (hmu : ∀ x : P.dom, mu * ‖(x : F)‖ ^ 2 ≤ quadForm P.op x) (k : FormSpace P) :
    (1 + mu) * ‖formExt P k‖ ^ 2 ≤ ‖k‖ ^ 2 := by
  refine UniformSpace.Completion.induction_on k ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro x
    have hnorm : ‖((x : FormSpace P))‖ = ‖x‖ := UniformSpace.Completion.norm_coe x
    have hsq := norm_sq_eq x
    have hq : (inner ℂ (toAmbient x) (P.op (toDom x)) : ℂ).re = quadForm P.op (toDom x) := by
      rw [quadForm, toAmbient_eq]
    have hb := hmu (toDom x)
    have hxa : ((toDom x : P.dom) : F) = toAmbient x := (toAmbient_eq x).symm
    rw [hxa] at hb
    rw [formExt_coe, hnorm, hsq, hq]
    linarith


#print axioms solution
