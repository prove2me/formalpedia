-- Prove2me | solution 1 for BirkhoffGlobalSection.variational_symplecticity_bundle
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T10:35:33.452692+00:00
-- url     : https://prove2.me/submissions/5b68b3f1-a9ff-4ddb-9cf4-48dffdf8b58b

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open BirkhoffGlobalSection Set Filter
open scoped ContDiff Topology
set_option maxHeartbeats 800000

private theorem unitThreeSphere_ne_zero (u : Phase) (hu : u ∈ unitThreeSphere) : u ≠ 0 := by
  intro h
  subst u
  norm_num [unitThreeSphere, zNormSq, wNormSq] at hu

/-- Product rule for the constant ambient symplectic form. -/
private theorem phase_symplectic_curve_derivative (v w : ℝ → Phase) (t : ℝ) (a b : Phase)
    (hv : HasDerivAt v a t) (hw : HasDerivAt w b t) :
    HasDerivAt (fun s => phaseSymplecticForm (v s) (w s))
      (phaseSymplecticForm a (w t) + phaseSymplecticForm (v t) b) t := by
  have h := BirkhoffGlobalSection.contact_variation_preservation_bundle.1 v w t a b hv hw
  have hd := h.mul_const (-2)
  convert! hd using 1
  · ext s
    simp only [phaseRadialContact, phaseSymplecticForm]
    ring
  · simp only [phaseRadialContact, phaseSymplecticForm]
    ring

/-- The coordinate Hamiltonian field represents the differential under omega. -/
private theorem hamiltonian_symplectic_differential (F : Phase → ℝ) (y v : Phase) :
    phaseSymplecticForm (hamiltonianVectorField F y) v = fderiv ℝ F y v := by
  have hv : v = v 0 • coordinateVector 0 + v 1 • coordinateVector 1 +
      v 2 • coordinateVector 2 + v 3 • coordinateVector 3 := by
    ext i
    fin_cases i <;> simp [coordinateVector]
  conv_rhs => rw [hv]
  simp [phaseSymplecticForm, hamiltonianVectorField, partialDerivative]
  ring

/-- The differential of a Hamiltonian field is paired with the Hessian. -/
private theorem hamiltonian_linearization_pairing (F : Phase → ℝ) (y v w : Phase)
    (hF : ContDiffAt ℝ ∞ F y) :
    phaseSymplecticForm (fderiv ℝ (hamiltonianVectorField F) y v) w =
      fderiv ℝ (fderiv ℝ F) y v w := by
  let γ : ℝ → Phase := fun s => y + s • v
  have hγ : HasDerivAt γ v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add
      ((hasDerivAt_id (0 : ℝ)).smul (hasDerivAt_const (0 : ℝ) v)) using 1
    simp
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ F) y := hF.fderiv_right (by simp)
  have hX := BirkhoffGlobalSection.model_contact_rate_bundle.1 F y hF
  have hXγ : DifferentiableAt ℝ (hamiltonianVectorField F) (γ 0) := by
    simpa [γ] using hX.differentiableAt (by simp)
  have hDγ : DifferentiableAt ℝ (fderiv ℝ F) (γ 0) := by
    simpa [γ] using hD.differentiableAt (by simp)
  have hl := phase_symplectic_curve_derivative
    (fun s => hamiltonianVectorField F (γ s)) (fun _ => w) 0
    (fderiv ℝ (hamiltonianVectorField F) y v) 0
    (by convert! hXγ.hasFDerivAt.comp_hasDerivAt 0 hγ using 1; simp [γ])
    (hasDerivAt_const 0 w)
  have hr := (hDγ.hasFDerivAt.comp_hasDerivAt 0 hγ).clm_apply
    (hasDerivAt_const 0 w)
  have he : (fun s => phaseSymplecticForm (hamiltonianVectorField F (γ s)) w) =
      (fun s => fderiv ℝ F (γ s) w) := by
    funext s
    exact hamiltonian_symplectic_differential F (γ s) w
  rw [he] at hl
  simpa [γ, phaseSymplecticForm] using hl.unique hr

/-- Hessian symmetry makes the Hamiltonian linearization infinitesimally symplectic. -/
private theorem hamiltonian_linearization_symplectic (F : Phase → ℝ) (y v w : Phase)
    (hF : ContDiffAt ℝ ∞ F y) :
    phaseSymplecticForm (fderiv ℝ (hamiltonianVectorField F) y v) w +
      phaseSymplecticForm v (fderiv ℝ (hamiltonianVectorField F) y w) = 0 := by
  have ha (a b : Phase) : phaseSymplecticForm a b = -phaseSymplecticForm b a := by
    simp only [phaseSymplecticForm]; ring
  rw [ha v, hamiltonian_linearization_pairing F y v w hF,
    hamiltonian_linearization_pairing F y w v hF]
  have htwo : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top
  rw [hF.isSymmSndFDerivAt htwo v w]
  ring

/-- Multiplying the field by any smooth rate preserves the infinitesimal pairing
on the tangent space to its energy level. -/
private theorem scaled_hamiltonian_linearization_symplectic (F b : Phase → ℝ) (y v w : Phase)
    (hF : ContDiffAt ℝ ∞ F y) (hb : DifferentiableAt ℝ b y)
    (hv : fderiv ℝ F y v = 0) (hw : fderiv ℝ F y w = 0) :
    phaseSymplecticForm (fderiv ℝ (fun x => b x • hamiltonianVectorField F x) y v) w +
      phaseSymplecticForm v (fderiv ℝ (fun x => b x • hamiltonianVectorField F x) y w) = 0 := by
  have hX := BirkhoffGlobalSection.model_contact_rate_bundle.1 F y hF
  rw [fderiv_fun_smul hb (hX.differentiableAt (by simp))]
  have hs := hamiltonian_linearization_symplectic F y v w hF
  have hv' := hamiltonian_symplectic_differential F y v
  have hw' := hamiltonian_symplectic_differential F y w
  simp only [hv, hw] at hv' hw'
  have he : phaseSymplecticForm
      ((b y) • fderiv ℝ (hamiltonianVectorField F) y v +
        fderiv ℝ b y v • hamiltonianVectorField F y) w +
      phaseSymplecticForm v ((b y) • fderiv ℝ (hamiltonianVectorField F) y w +
        fderiv ℝ b y w • hamiltonianVectorField F y) =
      b y * (phaseSymplecticForm (fderiv ℝ (hamiltonianVectorField F) y v) w +
        phaseSymplecticForm v (fderiv ℝ (hamiltonianVectorField F) y w)) +
      fderiv ℝ b y v * phaseSymplecticForm (hamiltonianVectorField F y) w -
      fderiv ℝ b y w * phaseSymplecticForm (hamiltonianVectorField F y) v := by
    simp only [phaseSymplecticForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simpa only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
    hs, hv', hw', mul_zero, add_zero, sub_zero] using he

/-- Any two supplied energy-tangent variations of a scaled Hamiltonian field
have constant ambient symplectic pairing. -/
private theorem scaled_hamiltonian_variation_pairing_conserved
    (F b : Phase → ℝ) (q v w : ℝ → Phase)
    (hF : ∀ t, ContDiffAt ℝ ∞ F (q t))
    (hb : ∀ t, DifferentiableAt ℝ b (q t))
    (hv : ∀ t, HasDerivAt v
      (fderiv ℝ (fun x => b x • hamiltonianVectorField F x) (q t) (v t)) t)
    (hw : ∀ t, HasDerivAt w
      (fderiv ℝ (fun x => b x • hamiltonianVectorField F x) (q t) (w t)) t)
    (hvE : ∀ t, fderiv ℝ F (q t) (v t) = 0)
    (hwE : ∀ t, fderiv ℝ F (q t) (w t) = 0) :
    ∀ t, phaseSymplecticForm (v t) (w t) = phaseSymplecticForm (v 0) (w 0) := by
  have hd (t : ℝ) : HasDerivAt (fun s => phaseSymplecticForm (v s) (w s)) 0 t := by
    have h := phase_symplectic_curve_derivative v w t _ _ (hv t) (hw t)
    rwa [scaled_hamiltonian_linearization_symplectic F b (q t) (v t) (w t)
      (hF t) (hb t) (hvE t) (hwE t)] at h
  intro t
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) t 0

set_option linter.unusedVariables false in
private theorem convex_model_contact_rate_regular : ∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y : Phase) (hy : y ∈ frontier M.body),
    let r : Phase → ℝ := fun x =>
      phaseRadialContact x (hamiltonianVectorField M.modelHamiltonian x)
    ContDiffAt ℝ ∞ (hamiltonianVectorField M.modelHamiltonian) y ∧
      ContDiffAt ℝ ∞ r y ∧ ContDiffAt ℝ ∞ (fun x => (r x)⁻¹) y ∧
      0 < (r y)⁻¹ := by
  exact BirkhoffGlobalSection.model_contact_rate_bundle.2.2.1

set_option linter.unusedVariables false in
private theorem radial_scale_contDiffAt : ∀ (a : Phase → ℝ) (u : Phase) (hu : u ≠ 0)
    (hG : ContDiffAt ℝ ∞ (fun x : Phase => a x • x) u),
    ContDiffAt ℝ ∞ a u := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.2.2.2.1

set_option linter.unusedVariables false in
private theorem convex_model_concrete_radial_variational_transport : ∀ {μ c : ℝ}
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
      (fderiv ℝ X (G (q t)) (fderiv ℝ G (q t) (v t))) t) := by
  exact BirkhoffGlobalSection.smooth_sphere_reeb_bundle.2.2.2.2.2.2.2.2.2.2.1

set_option linter.unusedVariables false in
private theorem convex_model_gauge_differential_energy_tangent : ∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v : Phase) (hu : u ∈ unitThreeSphere),
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    fderiv ℝ M.modelHamiltonian (G u) (fderiv ℝ G u v) = 0 := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.1

set_option linter.unusedVariables false in
private theorem convex_model_symplectic_contact_frame_pairing : ∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
    let A := convexModelSymplecticContactFrame M u 0
    let B := convexModelSymplecticContactFrame M u 1
    fderiv ℝ (fun x => f x * phaseRadialContact x B) u A -
      fderiv ℝ (fun x => f x * phaseRadialContact x A) u B = 1 := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.2.2.2.2.2.2.2.2.1

set_option linter.unusedVariables false in
private theorem convex_model_variation_contact : ∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q v : ℝ → Phase)
    (hqS : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ (convexModelSphereReebField M) (q t) (v t)) t)
    (h0 : q 0 0 * v 0 0 + q 0 1 * v 0 1 + q 0 2 * v 0 2 + q 0 3 * v 0 3 = 0)
    (hα0 : phaseRadialContact (q 0) (v 0) = 0),
    ∀ t, (q t 0 * v t 0 + q t 1 * v t 1 + q t 2 * v t 2 + q t 3 * v t 3 = 0) ∧
      phaseRadialContact (q t) (v t) = 0 := by
  exact BirkhoffGlobalSection.contact_variation_preservation_bundle.2.2.2.2.2.1

set_option linter.unusedVariables false in
private theorem convex_model_contact_variation_path_reconstruction : ∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (p : Plane),
    let e := p 0 • convexModelSymplecticContactFrame M (q 0) 0 +
      p 1 • convexModelSymplecticContactFrame M (q 0) 1
    ∀ t, (q t 0 * Z t e 0 + q t 1 * Z t e 1 +
        q t 2 * Z t e 2 + q t 3 * Z t e 3 = 0) ∧
      phaseRadialContact (q t) (Z t e) = 0 ∧
      Z t e = convexModelContactVariationPath M q Z t p 0 •
          convexModelSymplecticContactFrame M (q t) 0 +
        convexModelContactVariationPath M q Z t p 1 •
          convexModelSymplecticContactFrame M (q t) 1 := by
  exact BirkhoffGlobalSection.contact_variation_preservation_bundle.2.2.2.2.2.2.2.2.2.2

/-- The actual exterior derivative of the model contact form is conserved on
two initially sphere-tangent solutions of the concrete Reeb variational equation. -/
private theorem convex_model_variation_exterior_pairing_conserved {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q v w : ℝ → Phase)
    (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ (convexModelSphereReebField M) (q t) (v t)) t)
    (hw : ∀ t, HasDerivAt w (fderiv ℝ (convexModelSphereReebField M) (q t) (w t)) t)
    (hv0 : q 0 0 * v 0 0 + q 0 1 * v 0 1 + q 0 2 * v 0 2 + q 0 3 * v 0 3 = 0)
    (hw0 : q 0 0 * w 0 0 + q 0 1 * w 0 1 + q 0 2 * w 0 2 + q 0 3 * w 0 3 = 0) :
    let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
    ∀ t, (fderiv ℝ (fun x => f x * phaseRadialContact x (w t)) (q t) (v t) -
      fderiv ℝ (fun x => f x * phaseRadialContact x (v t)) (q t) (w t)) =
      (fderiv ℝ (fun x => f x * phaseRadialContact x (w 0)) (q 0) (v 0) -
      fderiv ℝ (fun x => f x * phaseRadialContact x (v 0)) (q 0) (w 0)) := by
  let a : Phase → ℝ := fun x => (gauge M.body x)⁻¹
  let G : Phase → Phase := fun x => a x • x
  let b : Phase → ℝ := fun x =>
    (phaseRadialContact x (hamiltonianVectorField M.modelHamiltonian x))⁻¹
  have hc := convex_model_smooth_radial_chart M
  have hg (t : ℝ) : G (q t) ∈ frontier M.body := (hc.2 _ (hs t)).2.1
  have hF (t : ℝ) : ContDiffAt ℝ ∞ M.modelHamiltonian (G (q t)) := by
    have hy := hg t
    rw [← M.image_frontier] at hy
    obtain ⟨s, h, he⟩ := hy
    have ht : G (q t) ∈ M.target := by
      rw [← he]
      exact M.toModel_mapsTo (M.contains_component h)
    exact M.model_smooth.contDiffAt (M.target_open.mem_nhds ht)
  have hb (t : ℝ) : DifferentiableAt ℝ b (G (q t)) :=
    (convex_model_contact_rate_regular M _ (hg t)).2.2.1.differentiableAt (by simp)
  have hvG := (convex_model_concrete_radial_variational_transport M q v hs hq hv hv0).2
  have hwG := (convex_model_concrete_radial_variational_transport M q w hs hq hw hw0).2
  have he := scaled_hamiltonian_variation_pairing_conserved M.modelHamiltonian b
    (fun t => G (q t)) (fun t => fderiv ℝ G (q t) (v t))
    (fun t => fderiv ℝ G (q t) (w t)) hF hb hvG hwG
    (fun t => convex_model_gauge_differential_energy_tangent M _ _ (hs t))
    (fun t => convex_model_gauge_differential_energy_tangent M _ _ (hs t))
  have ha (t : ℝ) : DifferentiableAt ℝ a (q t) :=
    (radial_scale_contDiffAt a (q t) (unitThreeSphere_ne_zero _ (hs t))
      (hc.2 _ (hs t)).1).differentiableAt (by simp)
  dsimp only
  intro t
  rw [BirkhoffGlobalSection.radial_characteristic_bundle.{0,0,0}.1 a _ _ _ (ha t),
    BirkhoffGlobalSection.radial_characteristic_bundle.{0,0,0}.1 a _ _ _ (ha 0)]
  exact congrArg Neg.neg (he t)

/-- A pairing-one frame identifies the pulled-back exterior form with standard area. -/
private theorem convex_model_frame_area_pairing {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere)
    (p r : Plane) :
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    let A := convexModelSymplecticContactFrame M u 0
    let B := convexModelSymplecticContactFrame M u 1
    (-phaseSymplecticForm (fderiv ℝ G u (p 0 • A + p 1 • B))
      (fderiv ℝ G u (r 0 • A + r 1 • B))) = p 0 * r 1 - p 1 * r 0 := by
  let a : Phase → ℝ := fun x => (gauge M.body x)⁻¹
  let G : Phase → Phase := fun x => a x • x
  let A := convexModelSymplecticContactFrame M u 0
  let B := convexModelSymplecticContactFrame M u 1
  have hc := convex_model_smooth_radial_chart M
  have ha : DifferentiableAt ℝ a u :=
    (radial_scale_contDiffAt a u (unitThreeSphere_ne_zero _ hu)
      (hc.2 _ hu).1).differentiableAt (by simp)
  have hp := convex_model_symplectic_contact_frame_pairing M u hu
  dsimp only at hp
  rw [BirkhoffGlobalSection.radial_characteristic_bundle.{0,0,0}.1 a u A B ha] at hp
  change -phaseSymplecticForm (fderiv ℝ G u A) (fderiv ℝ G u B) = 1 at hp
  have he : -phaseSymplecticForm (fderiv ℝ G u (p 0 • A + p 1 • B))
      (fderiv ℝ G u (r 0 • A + r 1 • B)) =
      (p 0 * r 1 - p 1 * r 0) * (-phaseSymplecticForm (fderiv ℝ G u A) (fderiv ℝ G u B)) := by
    simp only [map_add, map_smul, phaseSymplecticForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  dsimp only
  simpa only [hp, mul_one] using he

/-- The contact-coordinate action of a supplied fundamental solution preserves
standard area, hence is a genuine two-dimensional symplectic action. -/
private theorem convex_model_contact_variation_path_area_preserved {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (t : ℝ) (p r : Plane) :
    convexModelContactVariationPath M q Z t p 0 * convexModelContactVariationPath M q Z t r 1 -
      convexModelContactVariationPath M q Z t p 1 * convexModelContactVariationPath M q Z t r 0 =
      p 0 * r 1 - p 1 * r 0 := by
  let e (p : Plane) := p 0 • convexModelSymplecticContactFrame M (q 0) 0 +
    p 1 • convexModelSymplecticContactFrame M (q 0) 1
  have hrec (p : Plane) := convex_model_contact_variation_path_reconstruction M q Z hs hq hZ hZ0 p
  have hv (p : Plane) (t : ℝ) : HasDerivAt (fun s => Z s (e p))
      (fderiv ℝ (convexModelSphereReebField M) (q t) (Z t (e p))) t := by
    simpa only [ContinuousLinearMap.comp_apply, map_zero, add_zero] using
      (hZ t).clm_apply (hasDerivAt_const t (e p))
  have hpair := convex_model_variation_exterior_pairing_conserved M q
    (fun t => Z t (e p)) (fun t => Z t (e r)) hs hq (hv p) (hv r)
    (hrec p 0).1 (hrec r 0).1 t
  let a : Phase → ℝ := fun x => (gauge M.body x)⁻¹
  have hc := convex_model_smooth_radial_chart M
  have ha (t : ℝ) : DifferentiableAt ℝ a (q t) :=
    (radial_scale_contDiffAt a (q t) (unitThreeSphere_ne_zero _ (hs t))
      (hc.2 _ (hs t)).1).differentiableAt (by simp)
  dsimp only at hpair
  rw [BirkhoffGlobalSection.radial_characteristic_bundle.{0,0,0}.1 a _ _ _ (ha t),
    BirkhoffGlobalSection.radial_characteristic_bundle.{0,0,0}.1 a _ _ _ (ha 0)] at hpair
  rw [(hrec p t).2.2, (hrec r t).2.2] at hpair
  rw [convex_model_frame_area_pairing M _ (hs t)] at hpair
  simpa only [hZ0, ContinuousLinearMap.id_apply, e, a,
    convex_model_frame_area_pairing M _ (hs 0) p r] using hpair

/-- Area preservation alone forces injectivity on the coefficient plane. -/
private theorem plane_area_preserving_injective (A : Plane → Plane)
    (hA : ∀ p r, A p 0 * A r 1 - A p 1 * A r 0 = p 0 * r 1 - p 1 * r 0) :
    Function.Injective A := by
  intro p r h
  have he (s : Plane) : p 0 * s 1 - p 1 * s 0 = r 0 * s 1 - r 1 * s 0 := by
    rw [← hA p s, ← hA r s, h]
  have h0 := he ![0, 1]
  have h1 := he ![1, 0]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero, sub_zero,
    zero_sub] at h0 h1
  ext i
  fin_cases i
  · exact h0
  · exact neg_injective h1

/-- A linear area-preserving coefficient action is invertible. -/
private theorem plane_linear_area_preserving_bijective (A : Plane → Plane)
    (hlin : ∀ (p r : Plane) (a b : ℝ), A (a • p + b • r) = a • A p + b • A r)
    (harea : ∀ p r, A p 0 * A r 1 - A p 1 * A r 0 = p 0 * r 1 - p 1 * r 0) :
    Function.Bijective A := by
  let L : Plane →ₗ[ℝ] Plane :=
    { toFun := A
      map_add' := fun p r => by simpa using hlin p r 1 1
      map_smul' := fun a p => by simpa using hlin p 0 a 0 }
  have hi : Function.Injective L := plane_area_preserving_injective A harea
  exact ⟨hi, LinearMap.surjective_of_injective hi⟩

/-- Every time slice of the supplied contact variational path is invertible. -/
private theorem convex_model_contact_variation_path_bijective {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (t : ℝ) :
    Function.Bijective (convexModelContactVariationPath M q Z t) := by
  apply plane_linear_area_preserving_bijective
  · exact BirkhoffGlobalSection.contact_variation_preservation_bundle.2.2.2.2.2.2.2.1 M q Z t
  · exact convex_model_contact_variation_path_area_preserved M q Z hs hq hZ hZ0 t

/-- Nonzero initial coefficient vectors never vanish under the variational path. -/
private theorem convex_model_contact_variation_path_ne_zero {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (t : ℝ) (p : Plane) (hp : p ≠ 0) :
    convexModelContactVariationPath M q Z t p ≠ 0 := by
  have hz : convexModelContactVariationPath M q Z t 0 = 0 := by
    simp [convexModelContactVariationPath, convexModelContactCoordinates,
      transverseFrameCoordinates, dotProduct]
  intro h
  exact hp ((convex_model_contact_variation_path_bijective M q Z hs hq hZ hZ0 t).1 (h.trans hz.symm))



set_option linter.unusedVariables false in
theorem solution :
(∀ (v w : ℝ → Phase) (t : ℝ) (a b : Phase)
    (hv : HasDerivAt v a t) (hw : HasDerivAt w b t),
    HasDerivAt (fun s => phaseSymplecticForm (v s) (w s))
      (phaseSymplecticForm a (w t) + phaseSymplecticForm (v t) b) t) ∧
(∀ (F : Phase → ℝ) (y v : Phase),
    phaseSymplecticForm (hamiltonianVectorField F y) v = fderiv ℝ F y v) ∧
(∀ (F : Phase → ℝ) (y v w : Phase)
    (hF : ContDiffAt ℝ ∞ F y),
    phaseSymplecticForm (fderiv ℝ (hamiltonianVectorField F) y v) w =
      fderiv ℝ (fderiv ℝ F) y v w) ∧
(∀ (F : Phase → ℝ) (y v w : Phase)
    (hF : ContDiffAt ℝ ∞ F y),
    phaseSymplecticForm (fderiv ℝ (hamiltonianVectorField F) y v) w +
      phaseSymplecticForm v (fderiv ℝ (hamiltonianVectorField F) y w) = 0) ∧
(∀ (F b : Phase → ℝ) (y v w : Phase)
    (hF : ContDiffAt ℝ ∞ F y) (hb : DifferentiableAt ℝ b y)
    (hv : fderiv ℝ F y v = 0) (hw : fderiv ℝ F y w = 0),
    phaseSymplecticForm (fderiv ℝ (fun x => b x • hamiltonianVectorField F x) y v) w +
      phaseSymplecticForm v (fderiv ℝ (fun x => b x • hamiltonianVectorField F x) y w) = 0) ∧
(∀ (F b : Phase → ℝ) (q v w : ℝ → Phase)
    (hF : ∀ t, ContDiffAt ℝ ∞ F (q t))
    (hb : ∀ t, DifferentiableAt ℝ b (q t))
    (hv : ∀ t, HasDerivAt v
      (fderiv ℝ (fun x => b x • hamiltonianVectorField F x) (q t) (v t)) t)
    (hw : ∀ t, HasDerivAt w
      (fderiv ℝ (fun x => b x • hamiltonianVectorField F x) (q t) (w t)) t)
    (hvE : ∀ t, fderiv ℝ F (q t) (v t) = 0)
    (hwE : ∀ t, fderiv ℝ F (q t) (w t) = 0),
    ∀ t, phaseSymplecticForm (v t) (w t) = phaseSymplecticForm (v 0) (w 0)) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q v w : ℝ → Phase)
    (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ (convexModelSphereReebField M) (q t) (v t)) t)
    (hw : ∀ t, HasDerivAt w (fderiv ℝ (convexModelSphereReebField M) (q t) (w t)) t)
    (hv0 : q 0 0 * v 0 0 + q 0 1 * v 0 1 + q 0 2 * v 0 2 + q 0 3 * v 0 3 = 0)
    (hw0 : q 0 0 * w 0 0 + q 0 1 * w 0 1 + q 0 2 * w 0 2 + q 0 3 * w 0 3 = 0),
    let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
    ∀ t, (fderiv ℝ (fun x => f x * phaseRadialContact x (w t)) (q t) (v t) -
      fderiv ℝ (fun x => f x * phaseRadialContact x (v t)) (q t) (w t)) =
      (fderiv ℝ (fun x => f x * phaseRadialContact x (w 0)) (q 0) (v 0) -
      fderiv ℝ (fun x => f x * phaseRadialContact x (v 0)) (q 0) (w 0))) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere)
    (p r : Plane),
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    let A := convexModelSymplecticContactFrame M u 0
    let B := convexModelSymplecticContactFrame M u 1
    (-phaseSymplecticForm (fderiv ℝ G u (p 0 • A + p 1 • B))
      (fderiv ℝ G u (r 0 • A + r 1 • B))) = p 0 * r 1 - p 1 * r 0) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (t : ℝ) (p r : Plane),
    convexModelContactVariationPath M q Z t p 0 * convexModelContactVariationPath M q Z t r 1 -
      convexModelContactVariationPath M q Z t p 1 * convexModelContactVariationPath M q Z t r 0 =
      p 0 * r 1 - p 1 * r 0) ∧
(∀ (A : Plane → Plane)
    (hA : ∀ p r, A p 0 * A r 1 - A p 1 * A r 0 = p 0 * r 1 - p 1 * r 0),
    Function.Injective A) ∧
(∀ (A : Plane → Plane)
    (hlin : ∀ (p r : Plane) (a b : ℝ), A (a • p + b • r) = a • A p + b • A r)
    (harea : ∀ p r, A p 0 * A r 1 - A p 1 * A r 0 = p 0 * r 1 - p 1 * r 0),
    Function.Bijective A) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (t : ℝ),
    Function.Bijective (convexModelContactVariationPath M q Z t)) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (t : ℝ) (p : Plane) (hp : p ≠ 0),
    convexModelContactVariationPath M q Z t p ≠ 0) := by
  exact ⟨@phase_symplectic_curve_derivative, ⟨@hamiltonian_symplectic_differential, ⟨@hamiltonian_linearization_pairing, ⟨@hamiltonian_linearization_symplectic, ⟨@scaled_hamiltonian_linearization_symplectic, ⟨@scaled_hamiltonian_variation_pairing_conserved, ⟨@convex_model_variation_exterior_pairing_conserved, ⟨@convex_model_frame_area_pairing, ⟨@convex_model_contact_variation_path_area_preserved, ⟨@plane_area_preserving_injective, ⟨@plane_linear_area_preserving_bijective, ⟨@convex_model_contact_variation_path_bijective, @convex_model_contact_variation_path_ne_zero⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
