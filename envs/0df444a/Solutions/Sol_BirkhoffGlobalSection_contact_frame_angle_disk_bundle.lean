-- Prove2me | solution 1 for BirkhoffGlobalSection.contact_frame_angle_disk_bundle
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T20:25:02.33201+00:00
-- url     : https://prove2.me/submissions/a85197d0-5587-40e1-a705-1d025d3000e1

import Definitions.Def_BirkhoffGlobalSection_ContactVariationalInterfaces
import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
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

private theorem chart_variation_derivative : (∀ (f : Phase → Phase) (q v : ℝ → Phase)
    (t : ℝ) (a b : Phase) (hf : ContDiffAt ℝ ∞ f (q t))
    (hq : HasDerivAt q a t) (hv : HasDerivAt v b t),
    HasDerivAt (fun s => fderiv ℝ f (q s) (v s))
      (fderiv ℝ (fderiv ℝ f) (q t) a (v t) + fderiv ℝ f (q t) b) t) := by
  exact BirkhoffGlobalSection.radial_variation_bundle.1

private theorem chart_pushforward_tangent_derivative : (∀ (f R X : Phase → Phase) (u w : Phase) (γ : ℝ → Phase)
    (hf : ContDiffAt ℝ ∞ f u)
    (hR : DifferentiableAt ℝ R u) (hX : DifferentiableAt ℝ X (f u))
    (hγ0 : γ 0 = u) (hγ : HasDerivAt γ w 0)
    (heq : (fun s => fderiv ℝ f (γ s) (R (γ s))) =ᶠ[𝓝 0]
      (fun s => X (f (γ s)))),
    fderiv ℝ (fderiv ℝ f) u (R u) w + fderiv ℝ f u (fderiv ℝ R u w) =
      fderiv ℝ X (f u) (fderiv ℝ f u w)) := by
  exact BirkhoffGlobalSection.radial_variation_bundle.2.1

private theorem sphere_tangent_curve : (∀ (u w : Phase) (hu : u ∈ unitThreeSphere)
    (hw : u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0),
    ∃ γ : ℝ → Phase, γ 0 = u ∧ HasDerivAt γ w 0 ∧
      ∀ᶠ s in 𝓝 0, γ s ∈ unitThreeSphere) := by
  exact BirkhoffGlobalSection.radial_variation_bundle.2.2.1

private theorem sphere_chart_pushforward_tangent_derivative : (∀ (f R X : Phase → Phase) (u w : Phase) (hu : u ∈ unitThreeSphere)
    (hw : u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0)
    (hf : ContDiffAt ℝ ∞ f u)
    (hR : DifferentiableAt ℝ R u) (hX : DifferentiableAt ℝ X (f u))
    (hpush : ∀ z ∈ unitThreeSphere, fderiv ℝ f z (R z) = X (f z)),
    fderiv ℝ (fderiv ℝ f) u (R u) w + fderiv ℝ f u (fderiv ℝ R u w) =
      fderiv ℝ X (f u) (fderiv ℝ f u w)) := by
  exact BirkhoffGlobalSection.radial_variation_bundle.2.2.2.1

private theorem sphere_chart_variational_transport : (∀ (f R X : Phase → Phase) (q v : ℝ → Phase)
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
      (fderiv ℝ X (f (q t)) (fderiv ℝ f (q t) (v t))) t)) := by
  exact BirkhoffGlobalSection.radial_variation_bundle.2.2.2.2.1

private theorem convex_model_radial_variational_transport : (∀ {μ c : ℝ}
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
      (fderiv ℝ X (G (q t)) (fderiv ℝ G (q t) (v t))) t)) := by
  exact BirkhoffGlobalSection.radial_variation_bundle.2.2.2.2.2.1

private theorem convex_model_normalized_field_contDiffAt : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y : Phase) (hy : y ∈ frontier M.body),
    ContDiffAt ℝ ∞ (fun z =>
      (phaseRadialContact z (hamiltonianVectorField M.modelHamiltonian z))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian z) y) := by
  exact BirkhoffGlobalSection.radial_variation_bundle.2.2.2.2.2.2.1

private theorem convex_model_normalized_radial_variational_transport : (∀ {μ c : ℝ}
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
  exact BirkhoffGlobalSection.radial_variation_bundle.2.2.2.2.2.2.2

private theorem weighted_sphere_reeb_formula : (∀ (f : Phase → ℝ) (u : Phase)
    (hu : u ∈ unitThreeSphere) (hf : 0 < f u) (hdf : DifferentiableAt ℝ f u),
    let J : Phase → Phase := fun v => ![v 2, v 3, -v 0, -v 1]
    let L := fderiv ℝ f u
    let g : Phase := fun i => L (coordinateVector i)
    let R : Phase := ((f u) ^ 2)⁻¹ •
      ((2 * f u + L u) • J u - J g - L (J u) • u)
    (u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0) ∧
    (f u * phaseRadialContact u R = 1) ∧
    (∀ w : Phase,
      u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
      fderiv ℝ (fun x => f x * phaseRadialContact x w) u R -
        fderiv ℝ (fun x => f x * phaseRadialContact x R) u w = 0)) := by
  exact BirkhoffGlobalSection.weighted_reeb_bundle.1

private theorem weighted_sphere_reeb_exists_unique : (∀ (f : Phase → ℝ) (u : Phase)
    (hu : u ∈ unitThreeSphere) (hf : 0 < f u) (hdf : DifferentiableAt ℝ f u),
    ∃! R : Phase,
      u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0 ∧
      f u * phaseRadialContact u R = 1 ∧
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        fderiv ℝ (fun x => f x * phaseRadialContact x w) u R -
          fderiv ℝ (fun x => f x * phaseRadialContact x R) u w = 0)) := by
  exact BirkhoffGlobalSection.weighted_reeb_bundle.2.1

private theorem weighted_sphere_reeb_formula_smooth : (∀ (f : Phase → ℝ) (u : Phase)
    (hf : ContDiffAt ℝ ∞ f u) (hpos : 0 < f u),
    let J : Phase → Phase := fun v => ![v 2, v 3, -v 0, -v 1]
    let g : Phase → Phase := fun x i => fderiv ℝ f x (coordinateVector i)
    let R : Phase → Phase := fun x => ((f x) ^ 2)⁻¹ •
      ((2 * f x + fderiv ℝ f x x) • J x - J (g x) -
        (fderiv ℝ f x (J x)) • x)
    ContDiffAt ℝ ∞ R u) := by
  exact BirkhoffGlobalSection.weighted_reeb_bundle.2.2.1

private theorem gauge_inverse_sphere_reeb_exists_unique : (∀ (B : Set Phase)
    (h0 : B ∈ 𝓝 (0 : Phase)) (hb : Bornology.IsVonNBounded ℝ B)
    (u : Phase) (hu : u ∈ unitThreeSphere)
    (hG : ContDiffAt ℝ ∞ (fun x : Phase => (gauge B x)⁻¹ • x) u),
    let G : Phase → Phase := fun x => (gauge B x)⁻¹ • x
    let f : Phase → ℝ := fun x => zNormSq (G x) + wNormSq (G x)
    ∃! R : Phase,
      u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0 ∧
      f u * phaseRadialContact u R = 1 ∧
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        fderiv ℝ (fun x => f x * phaseRadialContact x w) u R -
          fderiv ℝ (fun x => f x * phaseRadialContact x R) u w = 0)) := by
  exact BirkhoffGlobalSection.weighted_reeb_bundle.2.2.2

private theorem radial_normalize_regular : (∀ (x : Phase) (hx : 0 < zNormSq x + wNormSq x),
    ContDiffAt ℝ ∞ radialNormalize x ∧ radialNormalize x ∈ unitThreeSphere) := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.1

private theorem radial_normalize_unit : (∀ (u : Phase) (hu : u ∈ unitThreeSphere),
    radialNormalize u = u) := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.2.1

private theorem sphere_reeb_extension_regular : (∀ (f : Phase → ℝ) (u : Phase)
    (hu : u ∈ unitThreeSphere) (hf : ContDiffAt ℝ ∞ f u) (hp : 0 < f u),
    ContDiffAt ℝ ∞ (sphereReebExtension f) u ∧
    (u 0 * sphereReebExtension f u 0 + u 1 * sphereReebExtension f u 1 +
      u 2 * sphereReebExtension f u 2 + u 3 * sphereReebExtension f u 3 = 0) ∧
    f u * phaseRadialContact u (sphereReebExtension f u) = 1 ∧
    (∀ w : Phase, u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
      fderiv ℝ (fun x => f x * phaseRadialContact x w) u (sphereReebExtension f u) -
        fderiv ℝ (fun x => f x * phaseRadialContact x (sphereReebExtension f u)) u w = 0)) := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.2.2.1

private theorem radial_scale_contDiffAt : (∀ (a : Phase → ℝ) (u : Phase) (hu : u ≠ 0)
    (hG : ContDiffAt ℝ ∞ (fun x : Phase => a x • x) u),
    ContDiffAt ℝ ∞ a u) := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.2.2.2.1

private theorem convex_model_sphere_weight_regular : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
    ContDiffAt ℝ ∞ f u ∧ 0 < f u) := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.2.2.2.2.1

private theorem convex_model_smooth_sphere_reeb_pushforward : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
    let R : Phase → Phase := sphereReebExtension f
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    let y := G u
    ContDiffAt ℝ ∞ R u ∧
      fderiv ℝ G u (R u) =
        (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
          hamiltonianVectorField M.modelHamiltonian y) := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.2.2.2.2.2.1

private theorem sphere_reeb_extension_orthogonal : (∀ (f : Phase → ℝ) (x : Phase)
    (hx : 0 < zNormSq x + wNormSq x)
    (hf : ContDiffAt ℝ ∞ f (radialNormalize x)) (hp : 0 < f (radialNormalize x)),
    x 0 * sphereReebExtension f x 0 + x 1 * sphereReebExtension f x 1 +
      x 2 * sphereReebExtension f x 2 + x 3 * sphereReebExtension f x 3 = 0) := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.2.2.2.2.2.2.1

private theorem orthogonal_field_derivative : (∀ (R : Phase → Phase) (u w : Phase)
    (hR : DifferentiableAt ℝ R u)
    (horth : (fun x => x 0 * R x 0 + x 1 * R x 1 +
      x 2 * R x 2 + x 3 * R x 3) =ᶠ[𝓝 u] (fun _ => (0 : ℝ))),
    w 0 * R u 0 + u 0 * (fderiv ℝ R u w) 0 +
    (w 1 * R u 1 + u 1 * (fderiv ℝ R u w) 1) +
    (w 2 * R u 2 + u 2 * (fderiv ℝ R u w) 2) +
    (w 3 * R u 3 + u 3 * (fderiv ℝ R u w) 3) = 0) := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.2.2.2.2.2.2.2.1

private theorem orthogonal_field_variation_tangent : (∀ (R : Phase → Phase) (q v : ℝ → Phase)
    (hq : ∀ t, HasDerivAt q (R (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ R (q t) (v t)) t)
    (hR : ∀ t, DifferentiableAt ℝ R (q t))
    (horth : ∀ t, (fun x => x 0 * R x 0 + x 1 * R x 1 +
      x 2 * R x 2 + x 3 * R x 3) =ᶠ[𝓝 (q t)] (fun _ => (0 : ℝ)))
    (h0 : q 0 0 * v 0 0 + q 0 1 * v 0 1 + q 0 2 * v 0 2 + q 0 3 * v 0 3 = 0),
    ∀ t, q t 0 * v t 0 + q t 1 * v t 1 + q t 2 * v t 2 + q t 3 * v t 3 = 0) := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.2.2.2.2.2.2.2.2.1

private theorem sphere_reeb_extension_variation_tangent : (∀ (f : Phase → ℝ) (q v : ℝ → Phase)
    (hf : ∀ u ∈ unitThreeSphere, ContDiffAt ℝ ∞ f u ∧ 0 < f u)
    (hqS : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (sphereReebExtension f (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ (sphereReebExtension f) (q t) (v t)) t)
    (h0 : q 0 0 * v 0 0 + q 0 1 * v 0 1 + q 0 2 * v 0 2 + q 0 3 * v 0 3 = 0),
    ∀ t, q t 0 * v t 0 + q t 1 * v t 1 + q t 2 * v t 2 + q t 3 * v t 3 = 0) := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.2.2.2.2.2.2.2.2.2.1

private theorem convex_model_concrete_radial_variational_transport : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q v : ℝ → Phase)
    (hqS : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ (convexModelSphereReebField M) (q t) (v t)) t)
    (h0 : q 0 0 * v 0 0 + q 0 1 * v 0 1 + q 0 2 * v 0 2 + q 0 3 * v 0 3 = 0),
    let G : Phase → Phase := fun u => (gauge M.body u)⁻¹ • u
    let X : Phase → Phase := fun y =>
      (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian y
    (∀ t, HasDerivAt (fun s => G (q s)) (X (G (q t))) t) ∧
    (∀ t, HasDerivAt (fun s => fderiv ℝ G (q s) (v s))
      (fderiv ℝ X (G (q t)) (fderiv ℝ G (q t) (v t))) t)) := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.2.2.2.2.2.2.2.2.2.2.1

private theorem convex_model_complete_concrete_sphere_reeb_trajectories : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    {φ : Flow ℝ (LeftEnergyState μ c)} (D : ConvexModelDynamics M φ),
    ∃ θ : Flow ℝ {u : Phase // u ∈ unitThreeSphere},
      ∀ u t, HasDerivAt (fun s => (θ s u : Phase))
        (convexModelSphereReebField M (θ t u)) t) := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.2.2.2.2.2.2.2.2.2.2.2

private theorem radial_contact_exterior_pullback : (∀ (a : Phase → ℝ) (u v w : Phase)
    (ha : DifferentiableAt ℝ a u),
    fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x w) u v -
      fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x v) u w =
    -phaseSymplecticForm
      (fderiv ℝ (fun x : Phase => a x • x) u v)
      (fderiv ℝ (fun x : Phase => a x • x) u w)) := by
  exact BirkhoffGlobalSection.radial_characteristic_bundle.{0,0,0}.1

private theorem radial_hamiltonian_reeb_transport : (∀ (a F : Phase → ℝ) (u T : Phase)
    (ha : DifferentiableAt ℝ a u)
    (ht : u 0 * T 0 + u 1 * T 1 + u 2 * T 2 + u 3 * T 3 = 0)
    (hpush : fderiv ℝ (fun x : Phase => a x • x) u T =
      hamiltonianVectorField F (a u • u))
    (hlevel : ∀ w : Phase,
      u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
      fderiv ℝ F (a u • u)
        (fderiv ℝ (fun x : Phase => a x • x) u w) = 0)
    (hpos : 0 < phaseRadialContact (a u • u)
      (hamiltonianVectorField F (a u • u))),
    let c := phaseRadialContact (a u • u) (hamiltonianVectorField F (a u • u))
    let R := c⁻¹ • T
    (u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0) ∧
      (a u)^2 * phaseRadialContact u R = 1 ∧
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x w) u R -
          fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x R) u w = 0)) := by
  exact BirkhoffGlobalSection.radial_characteristic_bundle.{0,0,0}.2.1

private theorem radial_boundary_tangent_lift : (∀ (a F : Phase → ℝ) (u X : Phase)
    (hu : u ∈ unitThreeSphere) (ha : DifferentiableAt ℝ a u) (hpos : 0 < a u)
    (hF : DifferentiableAt ℝ F (a u • u))
    (hzero : (fun x : Phase => F (a x • x)) =ᶠ[nhds u] (fun _ => (0 : ℝ)))
    (hrad : fderiv ℝ F (a u • u) u ≠ 0)
    (hX : fderiv ℝ F (a u • u) X = 0),
    let T := (a u)⁻¹ • X -
      ((a u)⁻¹ * (u 0 * X 0 + u 1 * X 1 + u 2 * X 2 + u 3 * X 3)) • u
    (u 0 * T 0 + u 1 * T 1 + u 2 * T 2 + u 3 * T 3 = 0) ∧
      fderiv ℝ (fun x : Phase => a x • x) u T = X ∧
      (∀ w : Phase, fderiv ℝ F (a u • u)
        (fderiv ℝ (fun x : Phase => a x • x) u w) = 0)) := by
  exact BirkhoffGlobalSection.radial_characteristic_bundle.{0,0,0}.2.2.1

private theorem convex_model_sphere_reeb_transport : (∀ {μ c : ℝ} (M : ConvexRegularizationModel μ c)
    (hcontact : ∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))
    (u : Phase) (hu : u ∈ unitThreeSphere),
    let a : Phase → ℝ := fun x => (gauge M.body x)⁻¹
    let G : Phase → Phase := fun x => a x • x
    let y := G u
    let X := hamiltonianVectorField M.modelHamiltonian y
    ∃ R : Phase,
      (u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0) ∧
      (a u)^2 * phaseRadialContact u R = 1 ∧
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x w) u R -
          fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x R) u w = 0) ∧
      fderiv ℝ G u R = (phaseRadialContact y X)⁻¹ • X) := by
  exact BirkhoffGlobalSection.radial_characteristic_bundle.{0,0,0}.2.2.2.1

private theorem hamiltonian_radial_contact_pairing : (∀ (F : Phase → ℝ) (y : Phase),
    phaseRadialContact y (hamiltonianVectorField F y) = fderiv ℝ F y y / 2) := by
  exact BirkhoffGlobalSection.radial_characteristic_bundle.{0,0,0}.2.2.2.2.1

private theorem convex_model_contact_positive_of_inward_negative : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    (hneg : ∀ y ∈ frontier M.body, ∀ t : ℝ, 0 ≤ t → t < 1 →
      M.modelHamiltonian (t • y) < 0),
    ∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y)) := by
  exact BirkhoffGlobalSection.radial_characteristic_bundle.{0,0,0}.2.2.2.2.2.1

private theorem local_inward_negative_derivative_nonnegative : (∀ (f : ℝ → ℝ) (d ε : ℝ)
    (hε : 0 < ε) (hd : HasDerivAt f d 1) (hzero : f 1 = 0)
    (hneg : ∀ t : ℝ, 1 - ε ≤ t → t < 1 → f t < 0),
    0 ≤ d) := by
  exact BirkhoffGlobalSection.radial_characteristic_bundle.{0,0,0}.2.2.2.2.2.2.1

private theorem radial_derivative_pos_of_local_inward_negative.{u} : (∀ {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ) (s : E)
    (hsne : s ≠ 0) (hc : ContDiffAt ℝ 2 F s) (hzero : F s = 0)
    (hneg : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 1 - ε ≤ t → t < 1 → F (t • s) < 0)
    (hcurv : ∀ v : E, v ≠ 0 → fderiv ℝ F s v = 0 →
      0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v),
    0 < fderiv ℝ F s s) := by
  exact BirkhoffGlobalSection.radial_characteristic_bundle.{u,u,u}.2.2.2.2.2.2.2.1

private theorem convex_model_contact_positive_of_local_inward_negative : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    (hneg : ∀ y ∈ frontier M.body, ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, 1 - ε ≤ t → t < 1 → M.modelHamiltonian (t • y) < 0),
    ∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y)) := by
  exact BirkhoffGlobalSection.radial_characteristic_bundle.{0,0,0}.2.2.2.2.2.2.2.2.1

private theorem local_inward_negative_of_radial_derivative_pos.{u} : (∀ {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ) (s : E)
    (hc : DifferentiableAt ℝ F s) (hzero : F s = 0)
    (hrad : 0 < fderiv ℝ F s s),
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 1 - ε ≤ t → t < 1 → F (t • s) < 0) := by
  exact BirkhoffGlobalSection.radial_characteristic_bundle.{u,u,u}.2.2.2.2.2.2.2.2.2.1

private theorem convex_model_contact_positive_iff_local_inward_negative : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c),
    (∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y)) ↔
    (∀ y ∈ frontier M.body, ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, 1 - ε ≤ t → t < 1 → M.modelHamiltonian (t • y) < 0)) := by
  exact BirkhoffGlobalSection.radial_characteristic_bundle.{0,0,0}.2.2.2.2.2.2.2.2.2.2.1

private theorem convex_radial_slice_mem_interior.{u} : (∀ {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E) (hK : Convex ℝ K)
    (h0 : (0 : E) ∈ interior K) (y : E) (hy : y ∈ closure K)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1),
    t • y ∈ interior K) := by
  exact BirkhoffGlobalSection.radial_characteristic_bundle.{u,u,u}.2.2.2.2.2.2.2.2.2.2.2.1

private theorem convex_model_contact_positive_of_local_interior_negative : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    (hneg : ∀ y ∈ frontier M.body, ∀ᶠ x in nhds y,
      x ∈ interior M.body → M.modelHamiltonian x < 0),
    ∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y)) := by
  exact BirkhoffGlobalSection.radial_characteristic_bundle.{0,0,0}.2.2.2.2.2.2.2.2.2.2.2.2

private theorem scaled_hamiltonian_first_integral : (∀ (F b : Phase → ℝ) (y : Phase),
    fderiv ℝ F y (b y • hamiltonianVectorField F y) = 0) := by
  exact BirkhoffGlobalSection.reverse_radial_variation_bundle.1

private theorem first_integral_variation_conserved : (∀ (F : Phase → ℝ) (X : Phase → Phase)
    (x v : ℝ → Phase) (hF : ∀ t, ContDiffAt ℝ ∞ F (x t))
    (hX : ∀ t, DifferentiableAt ℝ X (x t))
    (hx : ∀ t, HasDerivAt x (X (x t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ X (x t) (v t)) t)
    (hzero : ∀ t, (fun y => fderiv ℝ F y (X y)) =ᶠ[𝓝 (x t)] (fun _ => (0 : ℝ))),
    ∀ t, fderiv ℝ F (x t) (v t) = fderiv ℝ F (x 0) (v 0)) := by
  exact BirkhoffGlobalSection.reverse_radial_variation_bundle.2.1

private theorem convex_model_normalized_variation_energy_tangent : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (x v : ℝ → Phase)
    (hs : ∀ t, x t ∈ frontier M.body)
    (hx : ∀ t, HasDerivAt x
      ((phaseRadialContact (x t) (hamiltonianVectorField M.modelHamiltonian (x t)))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian (x t)) t)
    (hv : ∀ t, HasDerivAt v
      (fderiv ℝ (fun y =>
        (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
          hamiltonianVectorField M.modelHamiltonian y) (x t) (v t)) t)
    (h0 : fderiv ℝ M.modelHamiltonian (x 0) (v 0) = 0),
    ∀ t, fderiv ℝ M.modelHamiltonian (x t) (v t) = 0) := by
  exact BirkhoffGlobalSection.reverse_radial_variation_bundle.2.2.1

private theorem convex_model_gauge_chart_mem_frontier : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ≠ 0),
    (gauge M.body u)⁻¹ • u ∈ frontier M.body) := by
  exact BirkhoffGlobalSection.reverse_radial_variation_bundle.2.2.2.1

private theorem convex_model_frontier_tangent_curve : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y w : Phase) (hy : y ∈ frontier M.body)
    (hw : fderiv ℝ M.modelHamiltonian y w = 0),
    ∃ γ : ℝ → Phase, γ 0 = y ∧ HasDerivAt γ w 0 ∧
      ∀ᶠ s in 𝓝 0, γ s ∈ frontier M.body) := by
  exact BirkhoffGlobalSection.reverse_radial_variation_bundle.2.2.2.2.1

private theorem convex_model_radial_left_inverse_tangent : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u w : Phase) (hu : u ∈ unitThreeSphere)
    (hw : u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0),
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    fderiv ℝ radialNormalize (G u) (fderiv ℝ G u w) = w) := by
  exact BirkhoffGlobalSection.reverse_radial_variation_bundle.2.2.2.2.2.1

private theorem convex_model_normalized_field_inverse_pushforward : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y : Phase) (hy : y ∈ frontier M.body),
    fderiv ℝ radialNormalize y
      ((phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian y) =
      convexModelSphereReebField M (radialNormalize y)) := by
  exact BirkhoffGlobalSection.reverse_radial_variation_bundle.2.2.2.2.2.2.1

private theorem convex_model_radial_right_inverse_tangent : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y w : Phase) (hy : y ∈ frontier M.body)
    (hw : fderiv ℝ M.modelHamiltonian y w = 0),
    fderiv ℝ (fun x : Phase => (gauge M.body x)⁻¹ • x) (radialNormalize y)
      (fderiv ℝ radialNormalize y w) = w) := by
  exact BirkhoffGlobalSection.reverse_radial_variation_bundle.2.2.2.2.2.2.2.1

private theorem convex_model_inverse_variational_differential : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y w : Phase) (hy : y ∈ frontier M.body)
    (hw : fderiv ℝ M.modelHamiltonian y w = 0),
    let X : Phase → Phase := fun z =>
      (phaseRadialContact z (hamiltonianVectorField M.modelHamiltonian z))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian z
    fderiv ℝ (fderiv ℝ radialNormalize) y (X y) w +
      fderiv ℝ radialNormalize y (fderiv ℝ X y w) =
      fderiv ℝ (convexModelSphereReebField M) (radialNormalize y)
        (fderiv ℝ radialNormalize y w)) := by
  exact BirkhoffGlobalSection.reverse_radial_variation_bundle.2.2.2.2.2.2.2.2.1

private theorem sphere_curve_eventual_tangent : (∀ (q : ℝ → Phase) (v : Phase) (t : ℝ)
    (hq : ∀ᶠ s in 𝓝 t, q s ∈ unitThreeSphere) (hd : HasDerivAt q v t),
    q t 0 * v 0 + q t 1 * v 1 + q t 2 * v 2 + q t 3 * v 3 = 0) := by
  exact BirkhoffGlobalSection.reverse_radial_variation_bundle.2.2.2.2.2.2.2.2.2.1

private theorem convex_model_radial_inverse_maps_tangent : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y w : Phase) (hy : y ∈ frontier M.body)
    (hw : fderiv ℝ M.modelHamiltonian y w = 0),
    let u := radialNormalize y
    let v := fderiv ℝ radialNormalize y w
    u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0) := by
  exact BirkhoffGlobalSection.reverse_radial_variation_bundle.2.2.2.2.2.2.2.2.2.2.1

private theorem convex_model_reverse_radial_variational_transport : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (x v : ℝ → Phase)
    (hs : ∀ t, x t ∈ frontier M.body)
    (hx : ∀ t, HasDerivAt x
      ((phaseRadialContact (x t) (hamiltonianVectorField M.modelHamiltonian (x t)))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian (x t)) t)
    (hv : ∀ t, HasDerivAt v
      (fderiv ℝ (fun y =>
        (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
          hamiltonianVectorField M.modelHamiltonian y) (x t) (v t)) t)
    (h0 : fderiv ℝ M.modelHamiltonian (x 0) (v 0) = 0),
    let q : ℝ → Phase := fun t => radialNormalize (x t)
    let w : ℝ → Phase := fun t => fderiv ℝ radialNormalize (x t) (v t)
    (∀ t, q t ∈ unitThreeSphere) ∧
    (∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t) ∧
    (∀ t, HasDerivAt w (fderiv ℝ (convexModelSphereReebField M) (q t) (w t)) t) ∧
    (∀ t, q t 0 * w t 0 + q t 1 * w t 1 + q t 2 * w t 2 + q t 3 * w t 3 = 0) ∧
    (∀ t, fderiv ℝ (fun u : Phase => (gauge M.body u)⁻¹ • u) (q t) (w t) = v t)) := by
  exact BirkhoffGlobalSection.reverse_radial_variation_bundle.2.2.2.2.2.2.2.2.2.2.2

private theorem quaternionic_transverse_pair : (∀ (g : Phase),
    phaseSymplecticForm (TangentialHessian.frame g 1) (TangentialHessian.frame g 2) =
      -(zNormSq g + wNormSq g) ∧
    transverseFrameCoordinates g (TangentialHessian.frame g 1) = ![zNormSq g + wNormSq g, 0] ∧
    transverseFrameCoordinates g (TangentialHessian.frame g 2) = ![0, zNormSq g + wNormSq g]) := by
  exact BirkhoffGlobalSection.transverse_contact_frame_bundle.1

private theorem hamiltonian_quaternionic_transverse_tangent : (∀ (F : Phase → ℝ) (y : Phase),
    fderiv ℝ F y (TangentialHessian.frame (TangentialHessian.grad F y) 1) = 0 ∧
    fderiv ℝ F y (TangentialHessian.frame (TangentialHessian.grad F y) 2) = 0) := by
  exact BirkhoffGlobalSection.transverse_contact_frame_bundle.2.1

private theorem characteristic_contact_projection_properties : (∀ (F : Phase → ℝ) (y v : Phase)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y))
    (hv : fderiv ℝ F y v = 0),
    phaseRadialContact y (characteristicContactProjection F y v) = 0 ∧
    fderiv ℝ F y (characteristicContactProjection F y v) = 0 ∧
    transverseFrameCoordinates (TangentialHessian.grad F y)
      (characteristicContactProjection F y v) =
        transverseFrameCoordinates (TangentialHessian.grad F y) v) := by
  exact BirkhoffGlobalSection.transverse_contact_frame_bundle.2.2.1

private theorem hamiltonian_contact_frame_pairing : (∀ (F : Phase → ℝ) (y : Phase)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y)),
    phaseSymplecticForm (hamiltonianContactFrame F y 0) (hamiltonianContactFrame F y 1) =
      -(zNormSq (TangentialHessian.grad F y) + wNormSq (TangentialHessian.grad F y))) := by
  exact BirkhoffGlobalSection.transverse_contact_frame_bundle.2.2.2.1

private theorem hamiltonian_contact_frame_properties : (∀ (F : Phase → ℝ) (y : Phase)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y)) (i : Fin 2),
    fderiv ℝ F y (hamiltonianContactFrame F y i) = 0 ∧
      phaseRadialContact y (hamiltonianContactFrame F y i) = 0) := by
  exact BirkhoffGlobalSection.transverse_contact_frame_bundle.2.2.2.2.1

private theorem hamiltonian_contact_frame_coordinates : (∀ (F : Phase → ℝ) (y : Phase)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y)),
    let n := zNormSq (TangentialHessian.grad F y) + wNormSq (TangentialHessian.grad F y)
    transverseFrameCoordinates (TangentialHessian.grad F y) (hamiltonianContactFrame F y 0) = ![n, 0] ∧
    transverseFrameCoordinates (TangentialHessian.grad F y) (hamiltonianContactFrame F y 1) = ![0, n]) := by
  exact BirkhoffGlobalSection.transverse_contact_frame_bundle.2.2.2.2.2.1

private theorem hamiltonian_gradient_radius_positive : (∀ (F : Phase → ℝ) (y : Phase)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y)),
    0 < zNormSq (TangentialHessian.grad F y) + wNormSq (TangentialHessian.grad F y)) := by
  exact BirkhoffGlobalSection.transverse_contact_frame_bundle.2.2.2.2.2.2.1

private theorem convex_model_sphere_contact_frame_properties : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere) (i : Fin 2),
    let v := convexModelSphereContactFrame M u i
    (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0) ∧
      phaseRadialContact u v = 0 ∧
      fderiv ℝ (fun x : Phase => (gauge M.body x)⁻¹ • x) u v =
        hamiltonianContactFrame M.modelHamiltonian ((gauge M.body u)⁻¹ • u) i) := by
  exact BirkhoffGlobalSection.transverse_contact_frame_bundle.2.2.2.2.2.2.2.1

private theorem convex_model_sphere_contact_frame_pairing : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
    let A := convexModelSphereContactFrame M u 0
    let B := convexModelSphereContactFrame M u 1
    let y := (gauge M.body u)⁻¹ • u
    fderiv ℝ (fun x => f x * phaseRadialContact x B) u A -
      fderiv ℝ (fun x => f x * phaseRadialContact x A) u B =
        zNormSq (TangentialHessian.grad M.modelHamiltonian y) +
          wNormSq (TangentialHessian.grad M.modelHamiltonian y)) := by
  exact BirkhoffGlobalSection.transverse_contact_frame_bundle.2.2.2.2.2.2.2.2.1

private theorem convex_model_sphere_contact_frame_coordinates : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    let g := TangentialHessian.grad M.modelHamiltonian (G u)
    let n := zNormSq g + wNormSq g
    transverseFrameCoordinates g (fderiv ℝ G u (convexModelSphereContactFrame M u 0)) = ![n, 0] ∧
    transverseFrameCoordinates g (fderiv ℝ G u (convexModelSphereContactFrame M u 1)) = ![0, n]) := by
  exact BirkhoffGlobalSection.transverse_contact_frame_bundle.2.2.2.2.2.2.2.2.2.1

private theorem convex_model_sphere_contact_frame_independent : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere)
    (a b : ℝ) (hz : a • convexModelSphereContactFrame M u 0 +
      b • convexModelSphereContactFrame M u 1 = 0),
    a = 0 ∧ b = 0) := by
  exact BirkhoffGlobalSection.transverse_contact_frame_bundle.2.2.2.2.2.2.2.2.2.2.1

private theorem convex_model_sphere_contact_frame_positive : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
    let A := convexModelSphereContactFrame M u 0
    let B := convexModelSphereContactFrame M u 1
    0 < fderiv ℝ (fun x => f x * phaseRadialContact x B) u A -
      fderiv ℝ (fun x => f x * phaseRadialContact x A) u B) := by
  exact BirkhoffGlobalSection.transverse_contact_frame_bundle.2.2.2.2.2.2.2.2.2.2.2

private theorem differential_dot_gradient : (∀ (F : Phase → ℝ) (y v : Phase),
    fderiv ℝ F y v = v ⬝ᵥ TangentialHessian.grad F y) := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.1

private theorem quaternionic_vector_reconstruction : (∀ (g v : Phase),
    (zNormSq g + wNormSq g) • v = (v ⬝ᵥ g) • g +
      (v ⬝ᵥ TangentialHessian.frame g 0) • TangentialHessian.frame g 0 +
      (v ⬝ᵥ TangentialHessian.frame g 1) • TangentialHessian.frame g 1 +
      (v ⬝ᵥ TangentialHessian.frame g 2) • TangentialHessian.frame g 2) := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.1

private theorem characteristic_contact_projection_linear : (∀ (F : Phase → ℝ) (y v w : Phase) (a b : ℝ),
    characteristicContactProjection F y (a • v + b • w) =
      a • characteristicContactProjection F y v + b • characteristicContactProjection F y w) := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.1

private theorem hamiltonian_contact_frame_reconstruction : (∀ (F : Phase → ℝ) (y v : Phase)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y))
    (hv : fderiv ℝ F y v = 0) (hα : phaseRadialContact y v = 0),
    let g := TangentialHessian.grad F y
    let n := zNormSq g + wNormSq g
    let c := transverseFrameCoordinates g v
    v = (c 0 / n) • hamiltonianContactFrame F y 0 +
      (c 1 / n) • hamiltonianContactFrame F y 1) := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.1

private theorem convex_model_gauge_differential_energy_tangent : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v : Phase) (hu : u ∈ unitThreeSphere),
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    fderiv ℝ M.modelHamiltonian (G u) (fderiv ℝ G u v) = 0) := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.1

private theorem convex_model_sphere_contact_frame_reconstruction : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v : Phase) (hu : u ∈ unitThreeSphere)
    (hv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0)
    (hα : phaseRadialContact u v = 0),
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    let g := TangentialHessian.grad M.modelHamiltonian (G u)
    let n := zNormSq g + wNormSq g
    let c := transverseFrameCoordinates g (fderiv ℝ G u v)
    v = (c 0 / n) • convexModelSphereContactFrame M u 0 +
      (c 1 / n) • convexModelSphereContactFrame M u 1) := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.2.1

private theorem characteristic_contact_projection_contDiffAt : (∀ (F : Phase → ℝ) (V : Phase → Phase)
    (y : Phase) (hF : ContDiffAt ℝ ∞ F y) (hV : ContDiffAt ℝ ∞ V y)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y)),
    ContDiffAt ℝ ∞ (fun z => characteristicContactProjection F z (V z)) y) := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.2.2.1

private theorem hamiltonian_contact_frame_contDiffAt : (∀ (F : Phase → ℝ) (y : Phase)
    (hF : ContDiffAt ℝ ∞ F y)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y)) (i : Fin 2),
    ContDiffAt ℝ ∞ (fun z => hamiltonianContactFrame F z i) y) := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.2.2.2.1

private theorem convex_model_sphere_contact_frame_contDiffAt : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere) (i : Fin 2),
    ContDiffAt ℝ ∞ (fun z => convexModelSphereContactFrame M z i) u) := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.2.2.2.2.1

private theorem convex_model_frame_radius_regular : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    ContDiffAt ℝ ∞ (convexModelFrameRadius M) u ∧ 0 < convexModelFrameRadius M u) := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.2.2.2.2.2.1

private theorem convex_model_symplectic_contact_frame_contDiffAt : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere) (i : Fin 2),
    ContDiffAt ℝ ∞ (fun z => convexModelSymplecticContactFrame M z i) u) := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.2.2.2.2.2.2.1

private theorem weighted_contact_pair_rescale : (∀ (f : Phase → ℝ) (u v w : Phase) (a b : ℝ)
    (hf : DifferentiableAt ℝ f u),
    fderiv ℝ (fun x => f x * phaseRadialContact x (b • w)) u (a • v) -
      fderiv ℝ (fun x => f x * phaseRadialContact x (a • v)) u (b • w) =
      a * b * (fderiv ℝ (fun x => f x * phaseRadialContact x w) u v -
        fderiv ℝ (fun x => f x * phaseRadialContact x v) u w)) := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.2.2.2.2.2.2.2.1

private theorem convex_model_symplectic_contact_frame_pairing : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
    let A := convexModelSymplecticContactFrame M u 0
    let B := convexModelSymplecticContactFrame M u 1
    fderiv ℝ (fun x => f x * phaseRadialContact x B) u A -
      fderiv ℝ (fun x => f x * phaseRadialContact x A) u B = 1) := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem convex_model_symplectic_contact_frame_properties : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere) (i : Fin 2),
    let v := convexModelSymplecticContactFrame M u i
    (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0) ∧
      phaseRadialContact u v = 0) := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem convex_model_symplectic_contact_frame_reconstruction : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v : Phase) (hu : u ∈ unitThreeSphere)
    (hv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0)
    (hα : phaseRadialContact u v = 0),
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    let c := transverseFrameCoordinates (TangentialHessian.grad M.modelHamiltonian (G u)) (fderiv ℝ G u v)
    v = (c 0 / Real.sqrt (convexModelFrameRadius M u)) • convexModelSymplecticContactFrame M u 0 +
      (c 1 / Real.sqrt (convexModelFrameRadius M u)) • convexModelSymplecticContactFrame M u 1) := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem convex_model_symplectic_contact_frame_independent : (∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere)
    (a b : ℝ) (hz : a • convexModelSymplecticContactFrame M u 0 +
      b • convexModelSymplecticContactFrame M u 1 = 0),
    a = 0 ∧ b = 0) := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

private theorem transverse_coordinates_smul (g v : Phase) (a : ℝ) :
    transverseFrameCoordinates g (a • v) = a • transverseFrameCoordinates g v := by
  ext i
  fin_cases i <;> simp [transverseFrameCoordinates, dotProduct, Fin.sum_univ_succ] <;> ring

private theorem convex_model_contact_coordinates_linear {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v w : Phase) (a b : ℝ) :
    convexModelContactCoordinates M u (a • v + b • w) =
      a • convexModelContactCoordinates M u v + b • convexModelContactCoordinates M u w := by
  unfold convexModelContactCoordinates
  dsimp only
  rw [map_add, map_smul, map_smul]
  ext i
  fin_cases i <;> simp [transverseFrameCoordinates, dotProduct, Fin.sum_univ_succ] <;> ring

private theorem convex_model_contact_coordinates_frame {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere) :
    convexModelContactCoordinates M u (convexModelSymplecticContactFrame M u 0) = ![1, 0] ∧
    convexModelContactCoordinates M u (convexModelSymplecticContactFrame M u 1) = ![0, 1] := by
  have hr := (convex_model_frame_radius_regular M u hu).2
  have hs := Real.sq_sqrt hr.le
  have hsne := (Real.sqrt_pos.mpr hr).ne'
  have hn : (Real.sqrt (convexModelFrameRadius M u))⁻¹ *
      (Real.sqrt (convexModelFrameRadius M u))⁻¹ * convexModelFrameRadius M u = 1 := by
    calc
      _ = (Real.sqrt (convexModelFrameRadius M u))⁻¹ *
        (Real.sqrt (convexModelFrameRadius M u))⁻¹ * (Real.sqrt (convexModelFrameRadius M u))^2 := by rw [hs]
      _ = 1 := by field_simp
  have hc := convex_model_sphere_contact_frame_coordinates M u hu
  constructor
  · unfold convexModelContactCoordinates convexModelSymplecticContactFrame
    dsimp only
    rw [map_smul, transverse_coordinates_smul, hc.1]
    ext i
    fin_cases i <;> simp [convexModelFrameRadius, smul_eq_mul]
    simpa only [convexModelFrameRadius, mul_assoc] using hn
  · unfold convexModelContactCoordinates convexModelSymplecticContactFrame
    dsimp only
    rw [map_smul, transverse_coordinates_smul, hc.2]
    ext i
    fin_cases i <;> simp [convexModelFrameRadius, smul_eq_mul]
    simpa only [convexModelFrameRadius, mul_assoc] using hn

private theorem convex_model_contact_coordinates_reconstruction {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v : Phase) (hu : u ∈ unitThreeSphere)
    (hv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0)
    (hα : phaseRadialContact u v = 0) :
    v = (convexModelContactCoordinates M u v 0) • convexModelSymplecticContactFrame M u 0 +
      (convexModelContactCoordinates M u v 1) • convexModelSymplecticContactFrame M u 1 := by
  simpa [convexModelContactCoordinates, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    convex_model_symplectic_contact_frame_reconstruction M u v hu hv hα

private theorem convex_model_contact_coordinates_of_combination {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere) (a b : ℝ) :
    convexModelContactCoordinates M u (a • convexModelSymplecticContactFrame M u 0 +
      b • convexModelSymplecticContactFrame M u 1) = ![a, b] := by
  rw [convex_model_contact_coordinates_linear,
    (convex_model_contact_coordinates_frame M u hu).1,
    (convex_model_contact_coordinates_frame M u hu).2]
  ext i
  fin_cases i <;> simp

private theorem convex_model_contact_coordinates_zero_iff {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v : Phase) (hu : u ∈ unitThreeSphere)
    (hv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0)
    (hα : phaseRadialContact u v = 0) :
    convexModelContactCoordinates M u v = 0 ↔ v = 0 := by
  constructor
  · intro hz
    have h := convex_model_contact_coordinates_reconstruction M u v hu hv hα
    simpa only [hz, Pi.zero_apply, zero_smul, zero_add] using h
  · intro hz
    simp [hz, convexModelContactCoordinates, transverseFrameCoordinates]

private theorem positive_rescaling_polar_iff (p q : Plane) (a θ : ℝ)
    (ha : 0 < a) (hq : q = a • p) :
    (∃ r : ℝ, 0 < r ∧ p = ![r * Real.cos θ, r * Real.sin θ]) ↔
    (∃ r : ℝ, 0 < r ∧ q = ![r * Real.cos θ, r * Real.sin θ]) := by
  constructor
  · rintro ⟨r, hr, hp⟩
    refine ⟨a * r, mul_pos ha hr, ?_⟩
    rw [hq, hp]
    ext i
    fin_cases i <;> simp <;> ring
  · rintro ⟨r, hr, hp⟩
    refine ⟨a⁻¹ * r, mul_pos (inv_pos.mpr ha) hr, ?_⟩
    have he : p = a⁻¹ • q := by rw [hq, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
    rw [he, hp]
    ext i
    fin_cases i <;> simp <;> ring

private theorem positive_rescaling_angular_bound (p q : ℝ → Plane) (a : ℝ → ℝ) (T B : ℝ)
    (ha : ∀ t, 0 < a t) (heq : ∀ t, q t = a t • p t)
    (hbound : ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ p t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      B < θ T - θ 0) :
    ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ q t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      B < θ T - θ 0 := by
  intro θ hθ hpolar
  exact hbound θ hθ (fun t =>
    (positive_rescaling_polar_iff (p t) (q t) (a t) (θ t) (ha t) (heq t)).mpr (hpolar t))

private theorem convex_model_contact_coordinates_angular_bound {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q v : ℝ → Phase) (T B : ℝ)
    (hq : ∀ t, q t ∈ unitThreeSphere)
    (hbound : ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧
        transverseFrameCoordinates
          (TangentialHessian.grad M.modelHamiltonian ((gauge M.body (q t))⁻¹ • q t))
          (fderiv ℝ (fun x : Phase => (gauge M.body x)⁻¹ • x) (q t) (v t)) =
            ![r * Real.cos (θ t), r * Real.sin (θ t)]) → B < θ T - θ 0) :
    ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ convexModelContactCoordinates M (q t) (v t) =
        ![r * Real.cos (θ t), r * Real.sin (θ t)]) → B < θ T - θ 0 := by
  exact positive_rescaling_angular_bound _ _
    (fun t => (Real.sqrt (convexModelFrameRadius M (q t)))⁻¹) T B
    (fun t => inv_pos.mpr (Real.sqrt_pos.mpr (convex_model_frame_radius_regular M _ (hq t)).2))
    (fun _ => rfl) hbound

private theorem convex_model_symplectic_frame_continuous_along {A : Type*} [TopologicalSpace A]
    {μ c : ℝ} (M : ConvexRegularizationModel μ c) (d : A → Phase)
    (hd : Continuous d) (hs : ∀ z, d z ∈ unitThreeSphere) (i : Fin 2) :
    Continuous (fun z => convexModelSymplecticContactFrame M (d z) i) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (convex_model_symplectic_contact_frame_contDiffAt M (d z) (hs z) i).continuousAt.comp hd.continuousAt

private theorem convex_model_global_frame_extends_over_capping_disk {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (d : ClosedDiskPoint → Phase)
    (hd : Continuous d) (hs : ∀ z, d z ∈ unitThreeSphere)
    (γ : {z : ClosedDiskPoint // z ∈ closedDiskBoundary} → Phase)
    (hbd : ∀ z, d z.val = γ z) :
    ∃ E : ClosedDiskPoint → Fin 2 → Phase,
      (∀ i, Continuous (fun z => E z i)) ∧
      (∀ z i, (d z 0 * E z i 0 + d z 1 * E z i 1 +
        d z 2 * E z i 2 + d z 3 * E z i 3 = 0) ∧ phaseRadialContact (d z) (E z i) = 0) ∧
      (∀ z, let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
        fderiv ℝ (fun x => f x * phaseRadialContact x (E z 1)) (d z) (E z 0) -
          fderiv ℝ (fun x => f x * phaseRadialContact x (E z 0)) (d z) (E z 1) = 1) ∧
      (∀ z v, d z 0 * v 0 + d z 1 * v 1 + d z 2 * v 2 + d z 3 * v 3 = 0 →
        phaseRadialContact (d z) v = 0 →
        v = convexModelContactCoordinates M (d z) v 0 • E z 0 +
          convexModelContactCoordinates M (d z) v 1 • E z 1) ∧
      (∀ z (a b : ℝ), a • E z 0 + b • E z 1 = 0 → a = 0 ∧ b = 0) ∧
      (∀ z i, E z.val i = convexModelSymplecticContactFrame M (γ z) i) := by
  refine ⟨fun z i => convexModelSymplecticContactFrame M (d z) i, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact convex_model_symplectic_frame_continuous_along M d hd hs i
  · intro z i
    exact convex_model_symplectic_contact_frame_properties M (d z) (hs z) i
  · intro z
    exact convex_model_symplectic_contact_frame_pairing M (d z) (hs z)
  · intro z v hv hα
    exact convex_model_contact_coordinates_reconstruction M (d z) v (hs z) hv hα
  · intro z a b hz
    exact convex_model_symplectic_contact_frame_independent M (d z) (hs z) a b hz
  · intro z i
    dsimp only
    rw [hbd z]

private theorem convex_model_capping_frames_boundary_agree {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (d₁ d₂ : ClosedDiskPoint → Phase)
    (hbd : ∀ z : {z : ClosedDiskPoint // z ∈ closedDiskBoundary}, d₁ z.val = d₂ z.val) :
    ∀ z : {z : ClosedDiskPoint // z ∈ closedDiskBoundary}, ∀ i : Fin 2,
      convexModelSymplecticContactFrame M (d₁ z.val) i =
        convexModelSymplecticContactFrame M (d₂ z.val) i := by
  intro z i
  rw [hbd z]

theorem solution :
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v w : Phase) (a b : ℝ),
    convexModelContactCoordinates M u (a • v + b • w) =
      a • convexModelContactCoordinates M u v + b • convexModelContactCoordinates M u w) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    convexModelContactCoordinates M u (convexModelSymplecticContactFrame M u 0) = ![1, 0] ∧
    convexModelContactCoordinates M u (convexModelSymplecticContactFrame M u 1) = ![0, 1]) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v : Phase) (hu : u ∈ unitThreeSphere)
    (hv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0)
    (hα : phaseRadialContact u v = 0),
    v = (convexModelContactCoordinates M u v 0) • convexModelSymplecticContactFrame M u 0 +
      (convexModelContactCoordinates M u v 1) • convexModelSymplecticContactFrame M u 1) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere) (a b : ℝ),
    convexModelContactCoordinates M u (a • convexModelSymplecticContactFrame M u 0 +
      b • convexModelSymplecticContactFrame M u 1) = ![a, b]) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v : Phase) (hu : u ∈ unitThreeSphere)
    (hv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0)
    (hα : phaseRadialContact u v = 0),
    convexModelContactCoordinates M u v = 0 ↔ v = 0) ∧
(∀ (p q : Plane) (a θ : ℝ)
    (ha : 0 < a) (hq : q = a • p),
    (∃ r : ℝ, 0 < r ∧ p = ![r * Real.cos θ, r * Real.sin θ]) ↔
    (∃ r : ℝ, 0 < r ∧ q = ![r * Real.cos θ, r * Real.sin θ])) ∧
(∀ (p q : ℝ → Plane) (a : ℝ → ℝ) (T B : ℝ)
    (ha : ∀ t, 0 < a t) (heq : ∀ t, q t = a t • p t)
    (hbound : ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ p t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      B < θ T - θ 0),
    ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ q t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      B < θ T - θ 0) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q v : ℝ → Phase) (T B : ℝ)
    (hq : ∀ t, q t ∈ unitThreeSphere)
    (hbound : ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧
        transverseFrameCoordinates
          (TangentialHessian.grad M.modelHamiltonian ((gauge M.body (q t))⁻¹ • q t))
          (fderiv ℝ (fun x : Phase => (gauge M.body x)⁻¹ • x) (q t) (v t)) =
            ![r * Real.cos (θ t), r * Real.sin (θ t)]) → B < θ T - θ 0),
    ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ convexModelContactCoordinates M (q t) (v t) =
        ![r * Real.cos (θ t), r * Real.sin (θ t)]) → B < θ T - θ 0) ∧
(∀ {A : Type*} [TopologicalSpace A]
    {μ c : ℝ} (M : ConvexRegularizationModel μ c) (d : A → Phase)
    (hd : Continuous d) (hs : ∀ z, d z ∈ unitThreeSphere) (i : Fin 2),
    Continuous (fun z => convexModelSymplecticContactFrame M (d z) i)) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (d : ClosedDiskPoint → Phase)
    (hd : Continuous d) (hs : ∀ z, d z ∈ unitThreeSphere)
    (γ : {z : ClosedDiskPoint // z ∈ closedDiskBoundary} → Phase)
    (hbd : ∀ z, d z.val = γ z),
    ∃ E : ClosedDiskPoint → Fin 2 → Phase,
      (∀ i, Continuous (fun z => E z i)) ∧
      (∀ z i, (d z 0 * E z i 0 + d z 1 * E z i 1 +
        d z 2 * E z i 2 + d z 3 * E z i 3 = 0) ∧ phaseRadialContact (d z) (E z i) = 0) ∧
      (∀ z, let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
        fderiv ℝ (fun x => f x * phaseRadialContact x (E z 1)) (d z) (E z 0) -
          fderiv ℝ (fun x => f x * phaseRadialContact x (E z 0)) (d z) (E z 1) = 1) ∧
      (∀ z v, d z 0 * v 0 + d z 1 * v 1 + d z 2 * v 2 + d z 3 * v 3 = 0 →
        phaseRadialContact (d z) v = 0 →
        v = convexModelContactCoordinates M (d z) v 0 • E z 0 +
          convexModelContactCoordinates M (d z) v 1 • E z 1) ∧
      (∀ z (a b : ℝ), a • E z 0 + b • E z 1 = 0 → a = 0 ∧ b = 0) ∧
      (∀ z i, E z.val i = convexModelSymplecticContactFrame M (γ z) i)) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (d₁ d₂ : ClosedDiskPoint → Phase)
    (hbd : ∀ z : {z : ClosedDiskPoint // z ∈ closedDiskBoundary}, d₁ z.val = d₂ z.val),
    ∀ z : {z : ClosedDiskPoint // z ∈ closedDiskBoundary}, ∀ i : Fin 2,
      convexModelSymplecticContactFrame M (d₁ z.val) i =
        convexModelSymplecticContactFrame M (d₂ z.val) i) := by
  exact ⟨@convex_model_contact_coordinates_linear, ⟨@convex_model_contact_coordinates_frame, ⟨@convex_model_contact_coordinates_reconstruction, ⟨@convex_model_contact_coordinates_of_combination, ⟨@convex_model_contact_coordinates_zero_iff, ⟨@positive_rescaling_polar_iff, ⟨@positive_rescaling_angular_bound, ⟨@convex_model_contact_coordinates_angular_bound, ⟨@convex_model_symplectic_frame_continuous_along, ⟨@convex_model_global_frame_extends_over_capping_disk, @convex_model_capping_frames_boundary_agree⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
