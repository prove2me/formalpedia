-- Prove2me | solution 1 for BookProof.FriedrichsFormGap.friedrichs_quadForm_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:24:17.425491+00:00
-- url     : https://prove2.me/submissions/773586e6-d7db-4953-8a62-a33872660c05

-- Adapted from Leonardo Pedro, timepiece commit61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFriedrichsFormGap.lean
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
set_option autoImplicit false
open BookProof.HashimotoShiftInvert
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

private theorem formExt_coe (P : PosSymOp F) (x : FormDom P) :
    formExt P (x : FormSpace P) = toAmbient x := by
  have hi : IsUniformInducing (UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := FormDom P)) := by
    simpa [UniformSpace.Completion.coe_toComplL] using
      UniformSpace.Completion.isUniformInducing_coe (FormDom P)
  have := ContinuousLinearMap.extend_eq (incl P) (denseRange_toComplL P) hi x
  simpa [formExt, incl, inclLin, UniformSpace.Completion.coe_toComplL] using this

private theorem formSpace_norm_bound (P : PosSymOp F) {mu : ℝ}
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


private theorem invShiftOperator_apply (R : F →L[ℂ] F) (hinj : Function.Injective R) (γ : ℝ)
    (y : LinearMap.range (R : F →ₗ[ℂ] F)) :
    invShiftOperator R hinj γ y = preim R y - (γ : ℂ) • (y : F) := rfl
private theorem friedrichsResolvent_apply (P : PosSymOp F) (u : F) :
    friedrichsResolvent P u = formExt P (formRiesz P u) := rfl
private theorem inner_friedrichsResolvent (P : PosSymOp F) (u v : F) :
    (inner ℂ u (friedrichsResolvent P v) : ℂ) = inner ℂ (formRiesz P u) (formRiesz P v) := by
  rw [friedrichsResolvent_apply, formRiesz_spec]

theorem solution (P : PosSymOp F)
    (hinj : Function.Injective (friedrichsResolvent P)) {mu : ℝ}
    (hmu : ∀ x : P.dom, mu * ‖(x : F)‖ ^ 2 ≤ quadForm P.op x)
    (y : LinearMap.range ((friedrichsResolvent P) : F →ₗ[ℂ] F)) :
    mu * ‖(y : F)‖ ^ 2 ≤ quadForm (invShiftOperator (friedrichsResolvent P) hinj 1) y := by
  have hy : friedrichsResolvent P (preim (friedrichsResolvent P) y) = (y : F) :=
    preim_spec _ y
  -- the quadratic form of `A = S⁻¹ − 1` at `y = S u`
  have hq : quadForm (invShiftOperator (friedrichsResolvent P) hinj 1) y
      = (inner ℂ (y : F) (preim (friedrichsResolvent P) y) : ℂ).re - 1 * ‖(y : F)‖ ^ 2 := by
    rw [quadForm, invShiftOperator_apply, inner_sub_right, inner_smul_right, Complex.sub_re,
      inner_self_eq_norm_sq_to_K]
    congr 1
    simp [← Complex.ofReal_pow]
  -- `⟪y, u⟫ = ⟪S u, u⟫ = ‖formRiesz u‖²`
  have hyu : (inner ℂ (y : F) (preim (friedrichsResolvent P) y) : ℂ).re
      = ‖formRiesz P (preim (friedrichsResolvent P) y)‖ ^ 2 := by
    have h1 : (inner ℂ (y : F) (preim (friedrichsResolvent P) y) : ℂ)
        = starRingEnd ℂ (inner ℂ (preim (friedrichsResolvent P) y)
            (friedrichsResolvent P (preim (friedrichsResolvent P) y)) : ℂ) := by
      rw [← inner_conj_symm, hy]
    rw [h1, inner_friedrichsResolvent, Complex.conj_re]
    exact re_inner_self (F := FormSpace P) _
  -- and `formExt (formRiesz u) = S u = y`
  have hext : formExt P (formRiesz P (preim (friedrichsResolvent P) y)) = (y : F) := by
    rw [← hy, friedrichsResolvent_apply]
  have hbound := formSpace_norm_bound P hmu (formRiesz P (preim (friedrichsResolvent P) y))
  rw [hext] at hbound
  rw [hq, hyu]
  nlinarith [hbound]


#print axioms solution
