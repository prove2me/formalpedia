-- Prove2me | solution 1 for BirkhoffGlobalSection.positive_time_change_bundle
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T12:49:00.92145+00:00
-- url     : https://prove2.me/submissions/15b05e2d-13f1-457f-a7ce-bdb454487f21

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Module
import Definitions.Def_BirkhoffGlobalSection_ContactVariationalInterfaces
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false



private theorem transverse_frame_coordinates_hamiltonian_shear
    (F : Phase → ℝ) (y w : Phase) (c : ℝ) :
    transverseFrameCoordinates (TangentialHessian.grad F y)
      (w + c • hamiltonianVectorField F y) =
        transverseFrameCoordinates (TangentialHessian.grad F y) w := by
  ext i
  fin_cases i <;>
    simp [transverseFrameCoordinates, TangentialHessian.frame,
      TangentialHessian.qJ, TangentialHessian.qK, TangentialHessian.grad,
      hamiltonianVectorField, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

private theorem positive_time_change_shear_derivative
    (r k l : ℝ → ℝ) (hr : Continuous r) (hk : Continuous k)
    (hpos : ∀ t, 0 < r t) (hdr : ∀ t, HasDerivAt r (r t * l t) t) :
    let η : ℝ → ℝ := fun t => r t * ∫ s in (0 : ℝ)..t, k s / r s
    η 0 = 0 ∧ ∀ t, HasDerivAt η (k t + η t * l t) t := by
  dsimp only
  let I : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, k s / r s
  have hc : Continuous (fun s => k s / r s) := hk.div hr (fun t => ne_of_gt (hpos t))
  have hI (t : ℝ) : HasDerivAt I (k t / r t) t :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  refine ⟨by simp, ?_⟩
  intro t
  have h := (hdr t).mul (hI t)
  apply h.congr_deriv
  dsimp only [I]
  field_simp [ne_of_gt (hpos t)]
  ring

private theorem positive_time_change_variation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (X : E → E) (b : E → ℝ) (x u : ℝ → E) (τ : ℝ → ℝ)
    (hx : ∀ s, HasDerivAt x (X (x s)) s)
    (hu : ∀ s, HasDerivAt u (fderiv ℝ X (x s) (u s)) s)
    (hτ : ∀ t, HasDerivAt τ (b (x (τ t))) t)
    (hX : ∀ t, DifferentiableAt ℝ X (x (τ t)))
    (hb : ∀ t, DifferentiableAt ℝ b (x (τ t)))
    (hpos : ∀ t, 0 < b (x (τ t)))
    (hk : Continuous (fun t => fderiv ℝ b (x (τ t)) (u (τ t)))) :
    let η : ℝ → ℝ := fun t => b (x (τ t)) *
      ∫ s in (0 : ℝ)..t, fderiv ℝ b (x (τ s)) (u (τ s)) / b (x (τ s))
    let z : ℝ → E := fun t => u (τ t) + η t • X (x (τ t))
    η 0 = 0 ∧ z 0 = u (τ 0) ∧
      ∀ t, HasDerivAt z (fderiv ℝ (fun y => b y • X y) (x (τ t)) (z t)) t := by
  dsimp only
  let η : ℝ → ℝ := fun t => b (x (τ t)) *
    ∫ s in (0 : ℝ)..t, fderiv ℝ b (x (τ s)) (u (τ s)) / b (x (τ s))
  have hq (t : ℝ) : HasDerivAt (fun s => x (τ s))
      (b (x (τ t)) • X (x (τ t))) t := (hx (τ t)).scomp t (hτ t)
  have hr (t : ℝ) : HasDerivAt (fun s => b (x (τ s)))
      (b (x (τ t)) * fderiv ℝ b (x (τ t)) (X (x (τ t)))) t := by
    convert! (hb t).hasFDerivAt.comp_hasDerivAt t (hq t) using 1
    simp only [map_smul, smul_eq_mul]
  have hc : Continuous (fun t => b (x (τ t))) :=
    continuous_iff_continuousAt.mpr (fun t => (hr t).continuousAt)
  have hη := positive_time_change_shear_derivative
    (fun t => b (x (τ t))) (fun t => fderiv ℝ b (x (τ t)) (u (τ t)))
    (fun t => fderiv ℝ b (x (τ t)) (X (x (τ t)))) hc hk hpos hr
  have hzero : η 0 = 0 := hη.1
  refine ⟨hzero, by simp, ?_⟩
  intro t
  have hu' := (hu (τ t)).scomp t (hτ t)
  have hX' := (hX t).hasFDerivAt.comp_hasDerivAt t (hq t)
  have hz := HasDerivAt.add hu' (HasDerivAt.smul (hη.2 t) hX')
  apply hz.congr_deriv
  rw [fderiv_fun_smul (hb t) (hX t)]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul, Function.comp_apply]
  module

private theorem hamiltonian_positive_time_change_variational_transport
    (F : Phase → ℝ) (b : Phase → ℝ) (x : ℝ → Phase)
    (Y : ℝ → (Phase →L[ℝ] Phase)) (τ : ℝ → ℝ)
    (hx : ∀ s, HasDerivAt x (hamiltonianVectorField F (x s)) s)
    (hY : ∀ s, HasDerivAt Y
      ((fderiv ℝ (hamiltonianVectorField F) (x s)).comp (Y s)) s)
    (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase) (hτ0 : τ 0 = 0)
    (hτ : ∀ t, HasDerivAt τ (b (x (τ t))) t)
    (hX : ∀ t, DifferentiableAt ℝ (hamiltonianVectorField F) (x (τ t)))
    (hb : ∀ t, DifferentiableAt ℝ b (x (τ t)))
    (hpos : ∀ t, 0 < b (x (τ t)))
    (hk : ∀ v : Phase, Continuous (fun t => fderiv ℝ b (x (τ t)) (Y (τ t) v))) :
    ∀ v : Phase, ∃ z : ℝ → Phase,
      z 0 = v ∧
      (∀ t, HasDerivAt z
        (fderiv ℝ (fun y => b y • hamiltonianVectorField F y) (x (τ t)) (z t)) t) ∧
      (∀ t, transverseFrameCoordinates (TangentialHessian.grad F (x (τ t))) (z t) =
        transverseFrameCoordinates (TangentialHessian.grad F (x (τ t))) (Y (τ t) v)) := by
  intro v
  have hu (s : ℝ) : HasDerivAt (fun t => Y t v)
      (fderiv ℝ (hamiltonianVectorField F) (x s) (Y s v)) s := by
    simpa only [ContinuousLinearMap.comp_apply, map_zero, add_zero] using
      (hY s).clm_apply (hasDerivAt_const s v)
  have h := positive_time_change_variation (hamiltonianVectorField F) b x
    (fun t => Y t v) τ hx hu hτ hX hb hpos (hk v)
  let η : ℝ → ℝ := fun t => b (x (τ t)) *
    ∫ s in (0 : ℝ)..t, fderiv ℝ b (x (τ s)) (Y (τ s) v) / b (x (τ s))
  refine ⟨fun t => Y (τ t) v + η t • hamiltonianVectorField F (x (τ t)), ?_, h.2.2, ?_⟩
  · simp only [η, intervalIntegral.integral_same, mul_zero, zero_smul, add_zero,
      hτ0, hY0, ContinuousLinearMap.id_apply]
  · intro t
    exact transverse_frame_coordinates_hamiltonian_shear F (x (τ t)) (Y (τ t) v) (η t)

private theorem polar_angle_bound_reparametrization (p q : ℝ → Plane) (τ : ℝ ≃o ℝ)
    (T S B : ℝ) (hτ0 : τ 0 = 0) (hτS : τ S = T)
    (heq : ∀ t, q t = p (τ t))
    (hbound : ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ p t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      B < θ T - θ 0) :
    ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ q t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      B < θ S - θ 0 := by
  intro θ hθ hpolar
  have hsymm0 : τ.symm 0 = 0 := by
    simpa only [τ.symm_apply_apply] using (congrArg τ.symm hτ0).symm
  have hsymmT : τ.symm T = S := by
    rw [← hτS, τ.symm_apply_apply]
  have hp : ∀ t, ∃ r : ℝ, 0 < r ∧
      p t = ![r * Real.cos (θ (τ.symm t)), r * Real.sin (θ (τ.symm t))] := by
    intro t
    obtain ⟨r, hr, h⟩ := hpolar (τ.symm t)
    refine ⟨r, hr, ?_⟩
    simpa only [heq, τ.apply_symm_apply] using h
  have h := hbound (fun t => θ (τ.symm t)) (hθ.comp τ.symm.continuous) hp
  simpa only [hsymm0, hsymmT] using h

private theorem positive_time_change_variational_matrix_reverse {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (X : E → E) (b : E → ℝ) (x : ℝ → E) (C : ℝ ≃o ℝ)
    (Z : ℝ → (E →L[ℝ] E))
    (hx : ∀ t, HasDerivAt x (X (x t)) t)
    (hC : ∀ t, HasDerivAt C (b (x t))⁻¹ t)
    (hZ : ∀ t, HasDerivAt Z
      ((fderiv ℝ (fun y => b y • X y) (x (C.symm t))).comp (Z t)) t)
    (hX : ∀ t, DifferentiableAt ℝ X (x t))
    (hb : ∀ t, DifferentiableAt ℝ b (x t))
    (hne : ∀ t, b (x t) ≠ 0)
    (hk : Continuous (fun t => (b (x t))⁻¹ •
      ((fderiv ℝ b (x t)).comp (Z (C t))))) :
    let η : ℝ → (E →L[ℝ] ℝ) := fun t =>
      -(∫ s in (0 : ℝ)..t, (b (x s))⁻¹ • ((fderiv ℝ b (x s)).comp (Z (C s))))
    let Y : ℝ → (E →L[ℝ] E) := fun t => Z (C t) + (η t).smulRight (X (x t))
    Y 0 = Z (C 0) ∧
      ∀ t, HasDerivAt Y ((fderiv ℝ X (x t)).comp (Y t)) t := by
  dsimp only
  let K : ℝ → (E →L[ℝ] ℝ) := fun t => (b (x t))⁻¹ •
    ((fderiv ℝ b (x t)).comp (Z (C t)))
  let η : ℝ → (E →L[ℝ] ℝ) := fun t => -(∫ s in (0 : ℝ)..t, K s)
  have hη (t : ℝ) : HasDerivAt η (-K t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable 0 t)
      hk.aestronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt).neg
  have hη0 : η 0 = 0 := by simp [η]
  refine ⟨by simp, ?_⟩
  intro t
  have hZC : HasDerivAt (fun s => Z (C s))
      ((b (x t))⁻¹ • ((fderiv ℝ (fun y => b y • X y) (x t)).comp (Z (C t)))) t := by
    convert! (hZ (C t)).scomp t (hC t) using 1
    simp only [C.symm_apply_apply]
  have hXt := (hX t).hasFDerivAt.comp_hasDerivAt t (hx t)
  have hL := (ContinuousLinearMap.smulRightL ℝ E E).hasFDerivAt.comp_hasDerivAt t (hη t)
  have hRank := hL.clm_apply hXt
  have h := HasDerivAt.add hZC hRank
  apply h.congr_deriv
  rw [fderiv_fun_smul (hb t) (hX t)]
  ext v
  simp only [ContinuousLinearMap.smulRightL_apply_apply,
    ContinuousLinearMap.comp_apply, add_apply, smul_apply, map_add, map_smul,
    ContinuousLinearMap.smulRight_apply, neg_apply, Function.comp_apply, K]
  simp only [smul_eq_mul, smul_smul, smul_add,
    inv_mul_cancel₀ (hne t)]
  dsimp only [η, K]
  simp only [neg_apply]
  module

private theorem hamiltonian_transverse_winding_positive_time_change
    (F : Phase → ℝ) (b : Phase → ℝ) (x : ℝ → Phase) (C : ℝ ≃o ℝ)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (T S : ℝ)
    (hwind : HasTransverseWindingAboveOne F x T)
    (hx : ∀ t, HasDerivAt x (hamiltonianVectorField F (x t)) t)
    (hC0 : C 0 = 0) (hCT : C T = S)
    (hC : ∀ t, HasDerivAt C (b (x t))⁻¹ t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase)
    (hZ : ∀ t, HasDerivAt Z
      ((fderiv ℝ (fun y => b y • hamiltonianVectorField F y) (x (C.symm t))).comp (Z t)) t)
    (hX : ∀ t, DifferentiableAt ℝ (hamiltonianVectorField F) (x t))
    (hb : ∀ t, DifferentiableAt ℝ b (x t))
    (hpos : ∀ t, 0 < b (x t))
    (hk : Continuous (fun t => (b (x t))⁻¹ •
      ((fderiv ℝ b (x t)).comp (Z (C t)))))
    (v : Phase) (hv : fderiv ℝ F (x 0) v = 0)
    (hvn : transverseFrameCoordinates (TangentialHessian.grad F (x 0)) v ≠ 0) :
    ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧
        transverseFrameCoordinates (TangentialHessian.grad F (x (C.symm t))) (Z t v) =
          ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      2 * Real.pi < θ S - θ 0 := by
  let η : ℝ → (Phase →L[ℝ] ℝ) := fun t =>
    -(∫ s in (0 : ℝ)..t, (b (x s))⁻¹ • ((fderiv ℝ b (x s)).comp (Z (C s))))
  let Y : ℝ → (Phase →L[ℝ] Phase) := fun t =>
    Z (C t) + (η t).smulRight (hamiltonianVectorField F (x t))
  have hrev := positive_time_change_variational_matrix_reverse
    (hamiltonianVectorField F) b x C Z hx hC hZ hX hb (fun t => ne_of_gt (hpos t)) hk
  have hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase := by
    have hz : Y 0 = Z (C 0) := hrev.1
    exact hz.trans (by rw [hC0, hZ0])
  have heq (s : ℝ) :
      transverseFrameCoordinates (TangentialHessian.grad F (x s)) (Y s v) =
        transverseFrameCoordinates (TangentialHessian.grad F (x s)) (Z (C s) v) := by
    dsimp only [Y]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply]
    exact transverse_frame_coordinates_hamiltonian_shear F (x s) (Z (C s) v) (η s v)
  apply polar_angle_bound_reparametrization
    (fun s => transverseFrameCoordinates (TangentialHessian.grad F (x s)) (Y s v))
    (fun t => transverseFrameCoordinates (TangentialHessian.grad F (x (C.symm t))) (Z t v))
    C.symm T S (2 * Real.pi)
  · simpa only [C.symm_apply_apply] using (congrArg C.symm hC0).symm
  · rw [← hCT, C.symm_apply_apply]
  · intro t
    rw [heq, C.apply_symm_apply]
  · exact hwind Y hY0 hrev.2 v hv hvn

theorem solution :
(∀ (F : Phase → ℝ) (y w : Phase) (c : ℝ),
    transverseFrameCoordinates (TangentialHessian.grad F y)
      (w + c • hamiltonianVectorField F y) =
        transverseFrameCoordinates (TangentialHessian.grad F y) w) ∧
(∀ (r k l : ℝ → ℝ) (hr : Continuous r) (hk : Continuous k)
    (hpos : ∀ t, 0 < r t) (hdr : ∀ t, HasDerivAt r (r t * l t) t),
    let η : ℝ → ℝ := fun t => r t * ∫ s in (0 : ℝ)..t, k s / r s
    η 0 = 0 ∧ ∀ t, HasDerivAt η (k t + η t * l t) t) ∧
(∀ {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (X : E → E) (b : E → ℝ) (x u : ℝ → E) (τ : ℝ → ℝ)
    (hx : ∀ s, HasDerivAt x (X (x s)) s)
    (hu : ∀ s, HasDerivAt u (fderiv ℝ X (x s) (u s)) s)
    (hτ : ∀ t, HasDerivAt τ (b (x (τ t))) t)
    (hX : ∀ t, DifferentiableAt ℝ X (x (τ t)))
    (hb : ∀ t, DifferentiableAt ℝ b (x (τ t)))
    (hpos : ∀ t, 0 < b (x (τ t)))
    (hk : Continuous (fun t => fderiv ℝ b (x (τ t)) (u (τ t)))),
    let η : ℝ → ℝ := fun t => b (x (τ t)) *
      ∫ s in (0 : ℝ)..t, fderiv ℝ b (x (τ s)) (u (τ s)) / b (x (τ s))
    let z : ℝ → E := fun t => u (τ t) + η t • X (x (τ t))
    η 0 = 0 ∧ z 0 = u (τ 0) ∧
      ∀ t, HasDerivAt z (fderiv ℝ (fun y => b y • X y) (x (τ t)) (z t)) t) ∧
(∀ (F : Phase → ℝ) (b : Phase → ℝ) (x : ℝ → Phase)
    (Y : ℝ → (Phase →L[ℝ] Phase)) (τ : ℝ → ℝ)
    (hx : ∀ s, HasDerivAt x (hamiltonianVectorField F (x s)) s)
    (hY : ∀ s, HasDerivAt Y
      ((fderiv ℝ (hamiltonianVectorField F) (x s)).comp (Y s)) s)
    (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase) (hτ0 : τ 0 = 0)
    (hτ : ∀ t, HasDerivAt τ (b (x (τ t))) t)
    (hX : ∀ t, DifferentiableAt ℝ (hamiltonianVectorField F) (x (τ t)))
    (hb : ∀ t, DifferentiableAt ℝ b (x (τ t)))
    (hpos : ∀ t, 0 < b (x (τ t)))
    (hk : ∀ v : Phase, Continuous (fun t => fderiv ℝ b (x (τ t)) (Y (τ t) v))),
    ∀ v : Phase, ∃ z : ℝ → Phase,
      z 0 = v ∧
      (∀ t, HasDerivAt z
        (fderiv ℝ (fun y => b y • hamiltonianVectorField F y) (x (τ t)) (z t)) t) ∧
      (∀ t, transverseFrameCoordinates (TangentialHessian.grad F (x (τ t))) (z t) =
        transverseFrameCoordinates (TangentialHessian.grad F (x (τ t))) (Y (τ t) v))) ∧
(∀ (p q : ℝ → Plane) (τ : ℝ ≃o ℝ)
    (T S B : ℝ) (hτ0 : τ 0 = 0) (hτS : τ S = T)
    (heq : ∀ t, q t = p (τ t))
    (hbound : ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ p t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      B < θ T - θ 0),
    ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ q t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      B < θ S - θ 0) ∧
(∀ {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (X : E → E) (b : E → ℝ) (x : ℝ → E) (C : ℝ ≃o ℝ)
    (Z : ℝ → (E →L[ℝ] E))
    (hx : ∀ t, HasDerivAt x (X (x t)) t)
    (hC : ∀ t, HasDerivAt C (b (x t))⁻¹ t)
    (hZ : ∀ t, HasDerivAt Z
      ((fderiv ℝ (fun y => b y • X y) (x (C.symm t))).comp (Z t)) t)
    (hX : ∀ t, DifferentiableAt ℝ X (x t))
    (hb : ∀ t, DifferentiableAt ℝ b (x t))
    (hne : ∀ t, b (x t) ≠ 0)
    (hk : Continuous (fun t => (b (x t))⁻¹ •
      ((fderiv ℝ b (x t)).comp (Z (C t))))),
    let η : ℝ → (E →L[ℝ] ℝ) := fun t =>
      -(∫ s in (0 : ℝ)..t, (b (x s))⁻¹ • ((fderiv ℝ b (x s)).comp (Z (C s))))
    let Y : ℝ → (E →L[ℝ] E) := fun t => Z (C t) + (η t).smulRight (X (x t))
    Y 0 = Z (C 0) ∧
      ∀ t, HasDerivAt Y ((fderiv ℝ X (x t)).comp (Y t)) t) ∧
(∀ (F : Phase → ℝ) (b : Phase → ℝ) (x : ℝ → Phase) (C : ℝ ≃o ℝ)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (T S : ℝ)
    (hwind : HasTransverseWindingAboveOne F x T)
    (hx : ∀ t, HasDerivAt x (hamiltonianVectorField F (x t)) t)
    (hC0 : C 0 = 0) (hCT : C T = S)
    (hC : ∀ t, HasDerivAt C (b (x t))⁻¹ t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase)
    (hZ : ∀ t, HasDerivAt Z
      ((fderiv ℝ (fun y => b y • hamiltonianVectorField F y) (x (C.symm t))).comp (Z t)) t)
    (hX : ∀ t, DifferentiableAt ℝ (hamiltonianVectorField F) (x t))
    (hb : ∀ t, DifferentiableAt ℝ b (x t))
    (hpos : ∀ t, 0 < b (x t))
    (hk : Continuous (fun t => (b (x t))⁻¹ •
      ((fderiv ℝ b (x t)).comp (Z (C t)))))
    (v : Phase) (hv : fderiv ℝ F (x 0) v = 0)
    (hvn : transverseFrameCoordinates (TangentialHessian.grad F (x 0)) v ≠ 0),
    ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧
        transverseFrameCoordinates (TangentialHessian.grad F (x (C.symm t))) (Z t v) =
          ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      2 * Real.pi < θ S - θ 0) := by
  exact ⟨@transverse_frame_coordinates_hamiltonian_shear, ⟨@positive_time_change_shear_derivative, ⟨@positive_time_change_variation, ⟨@hamiltonian_positive_time_change_variational_transport, ⟨@polar_angle_bound_reparametrization, ⟨@positive_time_change_variational_matrix_reverse, @hamiltonian_transverse_winding_positive_time_change⟩⟩⟩⟩⟩⟩
