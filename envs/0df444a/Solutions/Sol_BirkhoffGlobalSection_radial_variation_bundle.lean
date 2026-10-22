-- Prove2me | solution 1 for BirkhoffGlobalSection.radial_variation_bundle
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T13:44:18.62399+00:00
-- url     : https://prove2.me/submissions/84674901-4092-406b-8a45-3a237694211e

import Theorems.Thm_BirkhoffGlobalSection_convex_model_smooth_radial_chart
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_BirkhoffGlobalSection_ContactVariationalInterfaces
import Theorems.Thm_BirkhoffGlobalSection_model_contact_rate_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false

private theorem transverse_frame_coordinates_hamiltonian_shear : (∀ (F : Phase → ℝ) (y w : Phase) (c : ℝ),
    transverseFrameCoordinates (TangentialHessian.grad F y)
      (w + c • hamiltonianVectorField F y) =
        transverseFrameCoordinates (TangentialHessian.grad F y) w) := by
  exact BirkhoffGlobalSection.positive_time_change_bundle.{0,0}.1

private theorem positive_time_change_shear_derivative : (∀ (r k l : ℝ → ℝ) (hr : Continuous r) (hk : Continuous k)
    (hpos : ∀ t, 0 < r t) (hdr : ∀ t, HasDerivAt r (r t * l t) t),
    let η : ℝ → ℝ := fun t => r t * ∫ s in (0 : ℝ)..t, k s / r s
    η 0 = 0 ∧ ∀ t, HasDerivAt η (k t + η t * l t) t) := by
  exact BirkhoffGlobalSection.positive_time_change_bundle.{0,0}.2.1

private theorem positive_time_change_variation.{u} : (∀ {E : Type u}
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
      ∀ t, HasDerivAt z (fderiv ℝ (fun y => b y • X y) (x (τ t)) (z t)) t) := by
  exact BirkhoffGlobalSection.positive_time_change_bundle.{u,u}.2.2.1

private theorem hamiltonian_positive_time_change_variational_transport : (∀ (F : Phase → ℝ) (b : Phase → ℝ) (x : ℝ → Phase)
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
        transverseFrameCoordinates (TangentialHessian.grad F (x (τ t))) (Y (τ t) v))) := by
  exact BirkhoffGlobalSection.positive_time_change_bundle.{0,0}.2.2.2.1

private theorem polar_angle_bound_reparametrization : (∀ (p q : ℝ → Plane) (τ : ℝ ≃o ℝ)
    (T S B : ℝ) (hτ0 : τ 0 = 0) (hτS : τ S = T)
    (heq : ∀ t, q t = p (τ t))
    (hbound : ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ p t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      B < θ T - θ 0),
    ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ q t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      B < θ S - θ 0) := by
  exact BirkhoffGlobalSection.positive_time_change_bundle.{0,0}.2.2.2.2.1

private theorem positive_time_change_variational_matrix_reverse.{u} : (∀ {E : Type u}
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
      ∀ t, HasDerivAt Y ((fderiv ℝ X (x t)).comp (Y t)) t) := by
  exact BirkhoffGlobalSection.positive_time_change_bundle.{u,u}.2.2.2.2.2.1

private theorem hamiltonian_transverse_winding_positive_time_change : (∀ (F : Phase → ℝ) (b : Phase → ℝ) (x : ℝ → Phase) (C : ℝ ≃o ℝ)
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
  exact BirkhoffGlobalSection.positive_time_change_bundle.{0,0}.2.2.2.2.2.2

private theorem hamiltonian_vector_field_contDiffAt : (∀ (F : Phase → ℝ) (y : Phase)
    (hF : ContDiffAt ℝ ∞ F y),
    ContDiffAt ℝ ∞ (hamiltonianVectorField F) y) := by
  exact BirkhoffGlobalSection.model_contact_rate_bundle.1

private theorem radial_contact_rate_contDiffAt : (∀ (X : Phase → Phase) (y : Phase)
    (hX : ContDiffAt ℝ ∞ X y),
    ContDiffAt ℝ ∞ (fun x => phaseRadialContact x (X x)) y) := by
  exact BirkhoffGlobalSection.model_contact_rate_bundle.2.1

private theorem convex_model_contact_rate_regular : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y : Phase) (hy : y ∈ frontier M.body),
    let r : Phase → ℝ := fun x =>
      phaseRadialContact x (hamiltonianVectorField M.modelHamiltonian x)
    ContDiffAt ℝ ∞ (hamiltonianVectorField M.modelHamiltonian) y ∧
      ContDiffAt ℝ ∞ r y ∧ ContDiffAt ℝ ∞ (fun x => (r x)⁻¹) y ∧
      0 < (r y)⁻¹) := by
  exact BirkhoffGlobalSection.model_contact_rate_bundle.2.2.1

private theorem time_change_functional_coefficient_continuous : (∀ (b : Phase → ℝ) (x : ℝ → Phase) (C : ℝ ≃o ℝ)
    (Z : ℝ → (Phase →L[ℝ] Phase))
    (hx : Continuous x) (hZ : Continuous Z)
    (hb : ∀ t, ContDiffAt ℝ ∞ b (x t)) (hne : ∀ t, b (x t) ≠ 0),
    Continuous (fun t => (b (x t))⁻¹ •
      ((fderiv ℝ b (x t)).comp (Z (C t))))) := by
  exact BirkhoffGlobalSection.model_contact_rate_bundle.2.2.2.1

private theorem convex_model_contact_time_change_regular : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (x : ℝ → Phase)
    (C : ℝ ≃o ℝ) (Z : ℝ → (Phase →L[ℝ] Phase))
    (hx : Continuous x) (hZ : Continuous Z)
    (hs : ∀ t, x t ∈ frontier M.body),
    let b : Phase → ℝ := fun y =>
      (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹
    (∀ t, DifferentiableAt ℝ (hamiltonianVectorField M.modelHamiltonian) (x t)) ∧
    (∀ t, DifferentiableAt ℝ b (x t)) ∧ (∀ t, 0 < b (x t)) ∧
    Continuous (fun t => (b (x t))⁻¹ •
      ((fderiv ℝ b (x t)).comp (Z (C t))))) := by
  exact BirkhoffGlobalSection.model_contact_rate_bundle.2.2.2.2.1

private theorem convex_model_contact_normalized_transverse_winding : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (x : ℝ → Phase) (C : ℝ ≃o ℝ)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (T S : ℝ)
    (hs : ∀ t, x t ∈ frontier M.body)
    (hwind : HasTransverseWindingAboveOne M.modelHamiltonian x T)
    (hx : ∀ t, HasDerivAt x (hamiltonianVectorField M.modelHamiltonian (x t)) t)
    (hC0 : C 0 = 0) (hCT : C T = S)
    (hC : ∀ t, HasDerivAt C
      (phaseRadialContact (x t) (hamiltonianVectorField M.modelHamiltonian (x t))) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase)
    (hZ : ∀ t, HasDerivAt Z
      ((fderiv ℝ (fun y =>
        (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
          hamiltonianVectorField M.modelHamiltonian y) (x (C.symm t))).comp (Z t)) t)
    (v : Phase) (hv : fderiv ℝ M.modelHamiltonian (x 0) v = 0)
    (hvn : transverseFrameCoordinates
      (TangentialHessian.grad M.modelHamiltonian (x 0)) v ≠ 0),
    ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧
        transverseFrameCoordinates
          (TangentialHessian.grad M.modelHamiltonian (x (C.symm t))) (Z t v) =
            ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      2 * Real.pi < θ S - θ 0) := by
  exact BirkhoffGlobalSection.model_contact_rate_bundle.2.2.2.2.2

private theorem chart_variation_derivative (f : Phase → Phase) (q v : ℝ → Phase)
    (t : ℝ) (a b : Phase) (hf : ContDiffAt ℝ ∞ f (q t))
    (hq : HasDerivAt q a t) (hv : HasDerivAt v b t) :
    HasDerivAt (fun s => fderiv ℝ f (q s) (v s))
      (fderiv ℝ (fderiv ℝ f) (q t) a (v t) + fderiv ℝ f (q t) b) t := by
  have hDs : ContDiffAt ℝ ∞ (fderiv ℝ f) (q t) :=
    hf.fderiv_right (by simp)
  have hD : DifferentiableAt ℝ (fderiv ℝ f) (q t) :=
    hDs.differentiableAt (by simp)
  exact (hD.hasFDerivAt.comp_hasDerivAt t hq).clm_apply hv

private theorem chart_pushforward_tangent_derivative
    (f R X : Phase → Phase) (u w : Phase) (γ : ℝ → Phase)
    (hf : ContDiffAt ℝ ∞ f u)
    (hR : DifferentiableAt ℝ R u) (hX : DifferentiableAt ℝ X (f u))
    (hγ0 : γ 0 = u) (hγ : HasDerivAt γ w 0)
    (heq : (fun s => fderiv ℝ f (γ s) (R (γ s))) =ᶠ[𝓝 0]
      (fun s => X (f (γ s)))) :
    fderiv ℝ (fderiv ℝ f) u (R u) w + fderiv ℝ f u (fderiv ℝ R u w) =
      fderiv ℝ X (f u) (fderiv ℝ f u w) := by
  have hfγ : ContDiffAt ℝ ∞ f (γ 0) := by simpa only [hγ0] using hf
  have hRγ : DifferentiableAt ℝ R (γ 0) := by simpa only [hγ0] using hR
  have hXγ : DifferentiableAt ℝ X (f (γ 0)) := by simpa only [hγ0] using hX
  have hleft := chart_variation_derivative f γ (fun s => R (γ s)) 0 w
    (fderiv ℝ R (γ 0) w) hfγ hγ (hRγ.hasFDerivAt.comp_hasDerivAt 0 hγ)
  have hright := hXγ.hasFDerivAt.comp_hasDerivAt 0
    (hfγ.differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt 0 hγ)
  have h := hleft.unique (hright.congr_of_eventuallyEq heq)
  simp only [hγ0] at h
  have htwo : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top
  rw [hf.isSymmSndFDerivAt htwo w (R u)] at h
  exact h

private theorem sphere_tangent_curve (u w : Phase) (hu : u ∈ unitThreeSphere)
    (hw : u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0) :
    ∃ γ : ℝ → Phase, γ 0 = u ∧ HasDerivAt γ w 0 ∧
      ∀ᶠ s in 𝓝 0, γ s ∈ unitThreeSphere := by
  let q : ℝ → Phase := fun s => u + s • w
  have hq : HasDerivAt q w 0 := by
    convert! (HasDerivAt.add (hasDerivAt_const (0 : ℝ) u)
      (HasDerivAt.smul (hasDerivAt_id (0 : ℝ)) (hasDerivAt_const (0 : ℝ) w))) using 1
    simp
  have hq0 : q 0 = u := by simp [q]
  have hc (i : Fin 4) : HasDerivAt (fun s => q s i) (w i) 0 :=
    (ContinuousLinearMap.proj i : Phase →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 hq
  have hs (i : Fin 4) := HasDerivAt.mul (hc i) (hc i)
  have hn : HasDerivAt (fun s => zNormSq (q s) + wNormSq (q s)) 0 0 := by
    convert! HasDerivAt.add (HasDerivAt.add (hs 0) (hs 1))
      (HasDerivAt.add (hs 2) (hs 3)) using 1
    · ext s; simp [zNormSq, wNormSq, pow_two]
    · simp only [hq0]; nlinarith [hw]
  have hunit : zNormSq u + wNormSq u = 1 := hu
  have hroot : HasDerivAt (fun s => Real.sqrt (zNormSq (q s) + wNormSq (q s))) 0 0 := by
    convert! (Real.hasDerivAt_sqrt (by rw [hq0, hunit]; norm_num)).comp 0 hn using 1
    simp only [hq0, hunit, Real.sqrt_one, mul_zero]
  have hinv := HasDerivAt.inv hroot (by rw [hq0, hunit, Real.sqrt_one]; norm_num)
  refine ⟨fun s => radialNormalize (q s), ?_, ?_, ?_⟩
  · simp [radialNormalize, hq0, hunit]
  · convert! HasDerivAt.smul hinv hq using 1
    simp [hq0, hunit]
  · have hp : ∀ᶠ s in 𝓝 0, 0 < zNormSq (q s) + wNormSq (q s) :=
      hn.continuousAt.eventually (isOpen_Ioi.mem_nhds (by
        change 0 < zNormSq (q 0) + wNormSq (q 0)
        rw [hq0, hunit]; norm_num))
    filter_upwards [hp] with s hspos
    change zNormSq (radialNormalize (q s)) + wNormSq (radialNormalize (q s)) = 1
    have hr := Real.sq_sqrt hspos.le
    have hrne : Real.sqrt (zNormSq (q s) + wNormSq (q s)) ≠ 0 :=
      (Real.sqrt_pos.mpr hspos).ne'
    simp only [radialNormalize, zNormSq, wNormSq, Pi.smul_apply, smul_eq_mul]
    simp only [zNormSq, wNormSq] at hr hrne
    field_simp
    nlinarith [hr]

private theorem sphere_chart_pushforward_tangent_derivative
    (f R X : Phase → Phase) (u w : Phase) (hu : u ∈ unitThreeSphere)
    (hw : u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0)
    (hf : ContDiffAt ℝ ∞ f u)
    (hR : DifferentiableAt ℝ R u) (hX : DifferentiableAt ℝ X (f u))
    (hpush : ∀ z ∈ unitThreeSphere, fderiv ℝ f z (R z) = X (f z)) :
    fderiv ℝ (fderiv ℝ f) u (R u) w + fderiv ℝ f u (fderiv ℝ R u w) =
      fderiv ℝ X (f u) (fderiv ℝ f u w) := by
  obtain ⟨γ, hγ0, hγ, hγs⟩ := sphere_tangent_curve u w hu hw
  apply chart_pushforward_tangent_derivative f R X u w γ hf hR hX hγ0 hγ
  filter_upwards [hγs] with s hs
  exact hpush (γ s) hs

private theorem sphere_chart_variational_transport
    (f R X : Phase → Phase) (q v : ℝ → Phase)
    (hqS : ∀ t, q t ∈ unitThreeSphere)
    (hvS : ∀ t, q t 0 * v t 0 + q t 1 * v t 1 +
      q t 2 * v t 2 + q t 3 * v t 3 = 0)
    (hf : ∀ t, ContDiffAt ℝ ∞ f (q t))
    (hR : ∀ t, DifferentiableAt ℝ R (q t))
    (hX : ∀ t, DifferentiableAt ℝ X (f (q t)))
    (hpush : ∀ z ∈ unitThreeSphere, fderiv ℝ f z (R z) = X (f z))
    (hq : ∀ t, HasDerivAt q (R (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ R (q t) (v t)) t) :
    (∀ t, HasDerivAt (fun s => f (q s)) (X (f (q t))) t) ∧
    (∀ t, HasDerivAt (fun s => fderiv ℝ f (q s) (v s))
      (fderiv ℝ X (f (q t)) (fderiv ℝ f (q t) (v t))) t) := by
  constructor
  · intro t
    rw [← hpush (q t) (hqS t)]
    exact ((hf t).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hq t)
  · intro t
    have hd := chart_variation_derivative f q v t (R (q t))
      (fderiv ℝ R (q t) (v t)) (hf t) (hq t) (hv t)
    rw [sphere_chart_pushforward_tangent_derivative f R X (q t) (v t)
      (hqS t) (hvS t) (hf t) (hR t) (hX t) hpush] at hd
    exact hd

private theorem convex_model_radial_variational_transport {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (R X : Phase → Phase) (q v : ℝ → Phase)
    (hqS : ∀ t, q t ∈ unitThreeSphere)
    (hvS : ∀ t, q t 0 * v t 0 + q t 1 * v t 1 +
      q t 2 * v t 2 + q t 3 * v t 3 = 0)
    (hR : ∀ t, DifferentiableAt ℝ R (q t))
    (hX : ∀ t, DifferentiableAt ℝ X ((gauge M.body (q t))⁻¹ • q t))
    (hpush : ∀ z ∈ unitThreeSphere,
      fderiv ℝ (fun u : Phase => (gauge M.body u)⁻¹ • u) z (R z) =
        X ((gauge M.body z)⁻¹ • z))
    (hq : ∀ t, HasDerivAt q (R (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ R (q t) (v t)) t) :
    let G : Phase → Phase := fun u => (gauge M.body u)⁻¹ • u
    (∀ t, HasDerivAt (fun s => G (q s)) (X (G (q t))) t) ∧
    (∀ t, HasDerivAt (fun s => fderiv ℝ G (q s) (v s))
      (fderiv ℝ X (G (q t)) (fderiv ℝ G (q t) (v t))) t) := by
  exact sphere_chart_variational_transport _ R X q v hqS hvS
    (fun t => ((convex_model_smooth_radial_chart M).2 (q t) (hqS t)).1)
    hR hX hpush hq hv

private theorem convex_model_normalized_field_contDiffAt {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y : Phase) (hy : y ∈ frontier M.body) :
    ContDiffAt ℝ ∞ (fun z =>
      (phaseRadialContact z (hamiltonianVectorField M.modelHamiltonian z))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian z) y := by
  have h := convex_model_contact_rate_regular M y hy
  exact h.2.2.1.smul h.1

private theorem convex_model_normalized_radial_variational_transport {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (R : Phase → Phase) (q v : ℝ → Phase)
    (hqS : ∀ t, q t ∈ unitThreeSphere)
    (hvS : ∀ t, q t 0 * v t 0 + q t 1 * v t 1 +
      q t 2 * v t 2 + q t 3 * v t 3 = 0)
    (hR : ∀ t, DifferentiableAt ℝ R (q t))
    (hpush : ∀ z ∈ unitThreeSphere,
      let y := (gauge M.body z)⁻¹ • z
      fderiv ℝ (fun u : Phase => (gauge M.body u)⁻¹ • u) z (R z) =
        (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
          hamiltonianVectorField M.modelHamiltonian y)
    (hq : ∀ t, HasDerivAt q (R (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ R (q t) (v t)) t) :
    let G : Phase → Phase := fun u => (gauge M.body u)⁻¹ • u
    let X : Phase → Phase := fun y =>
      (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian y
    (∀ t, HasDerivAt (fun s => G (q s)) (X (G (q t))) t) ∧
    (∀ t, HasDerivAt (fun s => fderiv ℝ G (q s) (v s))
      (fderiv ℝ X (G (q t)) (fderiv ℝ G (q t) (v t))) t) := by
  let X : Phase → Phase := fun y =>
    (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
      hamiltonianVectorField M.modelHamiltonian y
  have hX (t : ℝ) : DifferentiableAt ℝ X ((gauge M.body (q t))⁻¹ • q t) :=
    (convex_model_normalized_field_contDiffAt M _
      (((convex_model_smooth_radial_chart M).2 (q t) (hqS t)).2.1)).differentiableAt (by simp)
  exact convex_model_radial_variational_transport M R X q v hqS hvS hR hX hpush hq hv

theorem solution :
(∀ (f : Phase → Phase) (q v : ℝ → Phase)
    (t : ℝ) (a b : Phase) (hf : ContDiffAt ℝ ∞ f (q t))
    (hq : HasDerivAt q a t) (hv : HasDerivAt v b t),
    HasDerivAt (fun s => fderiv ℝ f (q s) (v s))
      (fderiv ℝ (fderiv ℝ f) (q t) a (v t) + fderiv ℝ f (q t) b) t) ∧
(∀ (f R X : Phase → Phase) (u w : Phase) (γ : ℝ → Phase)
    (hf : ContDiffAt ℝ ∞ f u)
    (hR : DifferentiableAt ℝ R u) (hX : DifferentiableAt ℝ X (f u))
    (hγ0 : γ 0 = u) (hγ : HasDerivAt γ w 0)
    (heq : (fun s => fderiv ℝ f (γ s) (R (γ s))) =ᶠ[𝓝 0]
      (fun s => X (f (γ s)))),
    fderiv ℝ (fderiv ℝ f) u (R u) w + fderiv ℝ f u (fderiv ℝ R u w) =
      fderiv ℝ X (f u) (fderiv ℝ f u w)) ∧
(∀ (u w : Phase) (hu : u ∈ unitThreeSphere)
    (hw : u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0),
    ∃ γ : ℝ → Phase, γ 0 = u ∧ HasDerivAt γ w 0 ∧
      ∀ᶠ s in 𝓝 0, γ s ∈ unitThreeSphere) ∧
(∀ (f R X : Phase → Phase) (u w : Phase) (hu : u ∈ unitThreeSphere)
    (hw : u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0)
    (hf : ContDiffAt ℝ ∞ f u)
    (hR : DifferentiableAt ℝ R u) (hX : DifferentiableAt ℝ X (f u))
    (hpush : ∀ z ∈ unitThreeSphere, fderiv ℝ f z (R z) = X (f z)),
    fderiv ℝ (fderiv ℝ f) u (R u) w + fderiv ℝ f u (fderiv ℝ R u w) =
      fderiv ℝ X (f u) (fderiv ℝ f u w)) ∧
(∀ (f R X : Phase → Phase) (q v : ℝ → Phase)
    (hqS : ∀ t, q t ∈ unitThreeSphere)
    (hvS : ∀ t, q t 0 * v t 0 + q t 1 * v t 1 +
      q t 2 * v t 2 + q t 3 * v t 3 = 0)
    (hf : ∀ t, ContDiffAt ℝ ∞ f (q t))
    (hR : ∀ t, DifferentiableAt ℝ R (q t))
    (hX : ∀ t, DifferentiableAt ℝ X (f (q t)))
    (hpush : ∀ z ∈ unitThreeSphere, fderiv ℝ f z (R z) = X (f z))
    (hq : ∀ t, HasDerivAt q (R (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ R (q t) (v t)) t),
    (∀ t, HasDerivAt (fun s => f (q s)) (X (f (q t))) t) ∧
    (∀ t, HasDerivAt (fun s => fderiv ℝ f (q s) (v s))
      (fderiv ℝ X (f (q t)) (fderiv ℝ f (q t) (v t))) t)) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (R X : Phase → Phase) (q v : ℝ → Phase)
    (hqS : ∀ t, q t ∈ unitThreeSphere)
    (hvS : ∀ t, q t 0 * v t 0 + q t 1 * v t 1 +
      q t 2 * v t 2 + q t 3 * v t 3 = 0)
    (hR : ∀ t, DifferentiableAt ℝ R (q t))
    (hX : ∀ t, DifferentiableAt ℝ X ((gauge M.body (q t))⁻¹ • q t))
    (hpush : ∀ z ∈ unitThreeSphere,
      fderiv ℝ (fun u : Phase => (gauge M.body u)⁻¹ • u) z (R z) =
        X ((gauge M.body z)⁻¹ • z))
    (hq : ∀ t, HasDerivAt q (R (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ R (q t) (v t)) t),
    let G : Phase → Phase := fun u => (gauge M.body u)⁻¹ • u
    (∀ t, HasDerivAt (fun s => G (q s)) (X (G (q t))) t) ∧
    (∀ t, HasDerivAt (fun s => fderiv ℝ G (q s) (v s))
      (fderiv ℝ X (G (q t)) (fderiv ℝ G (q t) (v t))) t)) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y : Phase) (hy : y ∈ frontier M.body),
    ContDiffAt ℝ ∞ (fun z =>
      (phaseRadialContact z (hamiltonianVectorField M.modelHamiltonian z))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian z) y) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (R : Phase → Phase) (q v : ℝ → Phase)
    (hqS : ∀ t, q t ∈ unitThreeSphere)
    (hvS : ∀ t, q t 0 * v t 0 + q t 1 * v t 1 +
      q t 2 * v t 2 + q t 3 * v t 3 = 0)
    (hR : ∀ t, DifferentiableAt ℝ R (q t))
    (hpush : ∀ z ∈ unitThreeSphere,
      let y := (gauge M.body z)⁻¹ • z
      fderiv ℝ (fun u : Phase => (gauge M.body u)⁻¹ • u) z (R z) =
        (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
          hamiltonianVectorField M.modelHamiltonian y)
    (hq : ∀ t, HasDerivAt q (R (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ R (q t) (v t)) t),
    let G : Phase → Phase := fun u => (gauge M.body u)⁻¹ • u
    let X : Phase → Phase := fun y =>
      (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian y
    (∀ t, HasDerivAt (fun s => G (q s)) (X (G (q t))) t) ∧
    (∀ t, HasDerivAt (fun s => fderiv ℝ G (q s) (v s))
      (fderiv ℝ X (G (q t)) (fderiv ℝ G (q t) (v t))) t)) := by
  exact ⟨@chart_variation_derivative, ⟨@chart_pushforward_tangent_derivative, ⟨@sphere_tangent_curve, ⟨@sphere_chart_pushforward_tangent_derivative, ⟨@sphere_chart_variational_transport, ⟨@convex_model_radial_variational_transport, ⟨@convex_model_normalized_field_contDiffAt, @convex_model_normalized_radial_variational_transport⟩⟩⟩⟩⟩⟩⟩
