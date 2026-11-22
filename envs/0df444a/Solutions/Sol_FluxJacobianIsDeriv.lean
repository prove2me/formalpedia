-- Prove2me | solution 1 for FluxJacobianIsDeriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:13:39.607846+00:00
-- url     : https://prove2.me/submissions/8b1a3cb4-8eaf-4f90-87f0-bb78de2a7502

import Definitions.Def_PHigherOrder_FluxJacobian
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Definitions.Def_PHigherOrder_FluxJacobianIsDeriv

set_option autoImplicit false

theorem _root_.solution (p : ℝ) :
    ∀ ξ : Plane, ξ ≠ 0 → HasFDerivAt (PFlux p) (FluxJacobian p ξ) ξ := by
  have hiSL : ∀ x y : Plane, (innerSL ℝ x) y = inner ℝ x y := fun _ _ => rfl
  -- The square-root-free form of the scalar factor.  Holds for EVERY `ζ`, including `0`.
  have hsqrpow : ∀ ζ : Plane, (‖ζ‖ ^ 2 : ℝ) ^ ((p - 2) / 2) = ‖ζ‖ ^ (p - 2) := by
    intro ζ
    rw [← Real.rpow_natCast ‖ζ‖ 2, ← Real.rpow_mul (norm_nonneg ζ)]
    congr 1
    push_cast
    ring
  have hPF : ∀ ζ : Plane, PFlux p ζ = (‖ζ‖ ^ 2 : ℝ) ^ ((p - 2) / 2) • ζ := by
    intro ζ
    rw [PFlux, hsqrpow]
  intro ξ hξ
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hn2 : (0 : ℝ) < ‖ξ‖ ^ 2 := by positivity
  have hn2ne : (‖ξ‖ ^ 2 : ℝ) ≠ 0 := ne_of_gt hn2
  have hsq : HasFDerivAt (fun ζ : Plane => ‖ζ‖ ^ 2) ((2 : ℝ) • innerSL ℝ ξ) ξ := by
    have hd : DifferentiableAt ℝ (fun ζ : Plane => ‖ζ‖ ^ 2) ξ :=
      ((contDiff_norm_sq ℝ (n := 1)).differentiable one_ne_zero) ξ
    have h := hd.hasFDerivAt
    rw [fderiv_norm_sq_apply] at h
    rw [two_smul ℝ (innerSL ℝ ξ)]
    rw [two_smul] at h
    exact h
  have hq : HasDerivAt (fun t : ℝ => t ^ ((p - 2) / 2))
      ((p - 2) / 2 * (‖ξ‖ ^ 2 : ℝ) ^ ((p - 2) / 2 - 1)) (‖ξ‖ ^ 2) :=
    Real.hasDerivAt_rpow_const (Or.inl hn2ne)
  have hprod := (hq.comp_hasFDerivAt ξ hsq).smul (hasFDerivAt_id ξ)
  have hfun : (((fun t : ℝ => t ^ ((p - 2) / 2)) ∘ fun ζ : Plane => ‖ζ‖ ^ 2) •
      (id : Plane → Plane)) = PFlux p := by
    funext ζ
    show (‖ζ‖ ^ 2 : ℝ) ^ ((p - 2) / 2) • ζ = PFlux p ζ
    rw [hPF ζ]
  rw [hfun] at hprod
  have hsplit : (‖ξ‖ ^ 2 : ℝ) ^ ((p - 2) / 2 - 1)
      = (‖ξ‖ ^ 2 : ℝ) ^ ((p - 2) / 2) / (‖ξ‖ ^ 2 : ℝ) := by
    rw [Real.rpow_sub hn2, Real.rpow_one]
  have hder : ((‖ξ‖ ^ 2 : ℝ) ^ ((p - 2) / 2)) • (ContinuousLinearMap.id ℝ Plane)
      + (((p - 2) / 2 * (‖ξ‖ ^ 2 : ℝ) ^ ((p - 2) / 2 - 1)) •
          ((2 : ℝ) • innerSL ℝ ξ)).smulRight ξ
      = FluxJacobian p ξ := by
    refine ContinuousLinearMap.ext fun w => ?_
    simp only [FluxJacobian, add_apply, FunLike.coe_smul,
      Pi.smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, hiSL, smul_smul]
    rw [hsplit, hsqrpow ξ]
    have hc : (p - 2) / 2 * (‖ξ‖ ^ (p - 2) / ‖ξ‖ ^ 2) * 2 * (inner ℝ ξ w : ℝ)
        = ‖ξ‖ ^ (p - 2) * ((p - 2) / ‖ξ‖ ^ 2 * (inner ℝ ξ w : ℝ)) := by
      field_simp
      try ring
    rw [smul_add, smul_smul, hc]
  rw [← hder]
  exact hprod
