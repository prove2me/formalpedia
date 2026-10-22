-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_sphere_reeb_transport_of_model_fields
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T08:04:08.834316+00:00
-- url     : https://prove2.me/submissions/fd2b2866-3b39-4ec7-b821-ee6d7c1c09c6

import Theorems.Thm_BirkhoffGlobalSection_convex_model_boundary_contact_positive
import Theorems.Thm_BirkhoffGlobalSection_weighted_radial_contact_exterior_derivative
import Theorems.Thm_BirkhoffGlobalSection_radial_rescaling_contact_pullback
import Theorems.Thm_BirkhoffGlobalSection_hamiltonian_radial_characteristic_normalization
import Theorems.Thm_BirkhoffGlobalSection_smooth_radial_gauge_chart

open BirkhoffGlobalSection
open scoped ContDiff Topology

/-- The exterior derivative of the pulled-back radial primitive is the
negative symplectic pairing of the derivative vectors. This ambient identity
requires only one derivative of the radial scale. -/
private theorem radial_contact_exterior_pullback (a : Phase → ℝ) (u v w : Phase)
    (ha : DifferentiableAt ℝ a u) :
    fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x w) u v -
      fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x v) u w =
    -phaseSymplecticForm
      (fderiv ℝ (fun x : Phase => a x • x) u v)
      (fderiv ℝ (fun x : Phase => a x • x) u w) := by
  have ha2 : DifferentiableAt ℝ (fun x => (a x)^2) u :=
    (ha.hasFDerivAt.pow 2).differentiableAt
  rw [weighted_radial_contact_exterior_derivative (fun x => (a x)^2) u v w ha2]
  have hpow : fderiv ℝ (fun x => (a x)^2) u = (2 * a u) • fderiv ℝ a u := by
    convert (ha.hasFDerivAt.pow 2).fderiv using 1
    simp
  have hid : DifferentiableAt ℝ (fun x : Phase => x) u := differentiableAt_id
  rw [hpow, fderiv_fun_smul ha hid]
  simp only [smul_apply, smul_eq_mul,
    add_apply, ContinuousLinearMap.smulRight_apply,
    fderiv_fun_id, ContinuousLinearMap.id_apply]
  simp [phaseRadialContact, phaseSymplecticForm]
  ring

/-- A sphere-tangent lift of the Hamiltonian vector becomes a normalized
Reeb vector after division by the positive boundary contact pairing.
The level-set tangent transport is an explicit geometric hypothesis. -/
private theorem radial_hamiltonian_reeb_transport (a F : Phase → ℝ) (u T : Phase)
    (ha : DifferentiableAt ℝ a u)
    (ht : u 0 * T 0 + u 1 * T 1 + u 2 * T 2 + u 3 * T 3 = 0)
    (hpush : fderiv ℝ (fun x : Phase => a x • x) u T =
      hamiltonianVectorField F (a u • u))
    (hlevel : ∀ w : Phase,
      u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
      fderiv ℝ F (a u • u)
        (fderiv ℝ (fun x : Phase => a x • x) u w) = 0)
    (hpos : 0 < phaseRadialContact (a u • u)
      (hamiltonianVectorField F (a u • u))) :
    let c := phaseRadialContact (a u • u) (hamiltonianVectorField F (a u • u))
    let R := c⁻¹ • T
    (u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0) ∧
      (a u)^2 * phaseRadialContact u R = 1 ∧
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x w) u R -
          fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x R) u w = 0) := by
  let c := phaseRadialContact (a u • u) (hamiltonianVectorField F (a u • u))
  let R := c⁻¹ • T
  have hnorm := hamiltonian_radial_characteristic_normalization F (a u • u) hpos
  have hpushR : fderiv ℝ (fun x : Phase => a x • x) u R =
      c⁻¹ • hamiltonianVectorField F (a u • u) := by
    simp only [R, map_smul, hpush]
  change _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    calc
      _ = c⁻¹ * (u 0 * T 0 + u 1 * T 1 + u 2 * T 2 + u 3 * T 3) := by ring
      _ = 0 := by rw [ht, mul_zero]
  · rw [← radial_rescaling_contact_pullback a u R ha, hpushR]
    exact hnorm.1
  · intro w hw
    rw [radial_contact_exterior_pullback a u R w ha, hpushR,
      hnorm.2.2.1 _ (hlevel w hw), neg_zero]

/-- A radial parametrization with constant boundary Hamiltonian lifts every
Hamiltonian-tangent vector to a sphere-tangent vector. The tangent-map
compatibilities are conclusions, not extra transport assumptions. -/
private theorem radial_boundary_tangent_lift (a F : Phase → ℝ) (u X : Phase)
    (hu : u ∈ unitThreeSphere) (ha : DifferentiableAt ℝ a u) (hpos : 0 < a u)
    (hF : DifferentiableAt ℝ F (a u • u))
    (hzero : (fun x : Phase => F (a x • x)) =ᶠ[nhds u] (fun _ => (0 : ℝ)))
    (hrad : fderiv ℝ F (a u • u) u ≠ 0)
    (hX : fderiv ℝ F (a u • u) X = 0) :
    let T := (a u)⁻¹ • X -
      ((a u)⁻¹ * (u 0 * X 0 + u 1 * X 1 + u 2 * X 2 + u 3 * X 3)) • u
    (u 0 * T 0 + u 1 * T 1 + u 2 * T 2 + u 3 * T 3 = 0) ∧
      fderiv ℝ (fun x : Phase => a x • x) u T = X ∧
      (∀ w : Phase, fderiv ℝ F (a u • u)
        (fderiv ℝ (fun x : Phase => a x • x) u w) = 0) := by
  let G : Phase → Phase := fun x => a x • x
  let L := fderiv ℝ a u
  let H := fderiv ℝ F (a u • u)
  let K := fderiv ℝ G u
  have hid : DifferentiableAt ℝ (fun x : Phase => x) u := differentiableAt_id
  have hG : DifferentiableAt ℝ G u := ha.smul hid
  have hconst : HasFDerivAt (fun _ : Phase => (0 : ℝ)) (0 : Phase →L[ℝ] ℝ) u :=
    hasFDerivAt_const (0 : ℝ) u
  have hc : HasFDerivAt (fun x : Phase => F (G x)) 0 u :=
    hconst.congr_of_eventuallyEq hzero
  have hchain := hF.hasFDerivAt.comp (f := G) u hG.hasFDerivAt
  have hHK : H.comp K = 0 := hchain.unique hc
  have hlevel (v : Phase) : H (K v) = 0 := by
    change (H.comp K) v = 0
    rw [hHK]
    rfl
  have hK (v : Phase) : K v = L v • u + a u • v := by
    dsimp only [K, G, L]
    rw [fderiv_fun_smul ha hid]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, fderiv_fun_id, ContinuousLinearMap.id_apply]
    exact add_comm _ _
  have hLX : L X = 0 := by
    have h := hlevel X
    rw [hK, map_add, map_smul, map_smul, hX, smul_eq_mul, smul_eq_mul,
      mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hrad
  have hLu : L u = -a u := by
    have h := hlevel u
    rw [hK, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
    have hz : (L u + a u) * H u = 0 := by nlinarith [h]
    have he := (mul_eq_zero.mp hz).resolve_right hrad
    linarith
  have hKu : K u = 0 := by rw [hK, hLu, neg_smul, neg_add_cancel]
  have hKX : K X = a u • X := by rw [hK, hLX, zero_smul, zero_add]
  let T := (a u)⁻¹ • X -
    ((a u)⁻¹ * (u 0 * X 0 + u 1 * X 1 + u 2 * X 2 + u 3 * X 3)) • u
  change _ ∧ K T = X ∧ ∀ w, H (K w) = 0
  refine ⟨?_, ?_, hlevel⟩
  · have hunit : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 = 1 := by
      have h := hu
      change zNormSq u + wNormSq u = 1 at h
      simpa only [zNormSq, wNormSq, add_assoc] using h
    have heq : u 0 * T 0 + u 1 * T 1 + u 2 * T 2 + u 3 * T 3 =
        (a u)⁻¹ * (u 0 * X 0 + u 1 * X 1 + u 2 * X 2 + u 3 * X 3) *
          (1 - (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2)) := by
      simp only [T, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq, hunit, sub_self, mul_zero]
  · rw [map_sub, map_smul, map_smul, hKX, hKu, smul_zero, sub_zero,
      smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]

private theorem gauge_inverse_frontier (B : Set Phase) (hc : Convex ℝ B)
    (h0 : B ∈ nhds (0 : Phase)) (hb : Bornology.IsVonNBounded ℝ B)
    (x : Phase) (hx : x ≠ 0) : (gauge B x)⁻¹ • x ∈ frontier B := by
  have hg : 0 < gauge B x := (gauge_pos (absorbent_nhds_zero h0) hb).2 hx
  apply (gauge_eq_one_iff_mem_frontier hc h0).mp
  rw [gauge_smul_of_nonneg (inv_nonneg.mpr hg.le), smul_eq_mul, inv_mul_cancel₀ hg.ne']

private theorem gauge_inverse_scale_differentiable (B : Set Phase) (u : Phase)
    (hu : u ≠ 0) (hG : DifferentiableAt ℝ (fun x : Phase => (gauge B x)⁻¹ • x) u) :
    DifferentiableAt ℝ (fun x : Phase => (gauge B x)⁻¹) u := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, u i ≠ 0 := by
    by_contra! h
    exact hu (funext h)
  let G : Phase → Phase := fun x => (gauge B x)⁻¹ • x
  have hdcomp : DifferentiableAt ℝ (fun x => G x i) u := differentiableAt_pi.mp hG i
  have hdcoord : DifferentiableAt ℝ (fun x : Phase => x i) u :=
    (hasFDerivAt_apply i u).differentiableAt
  have hratio : DifferentiableAt ℝ (fun x => G x i / x i) u := by
    convert! hdcomp.mul (hdcoord.inv hi) using 1
  have hne : ∀ᶠ x in nhds u, x i ≠ 0 :=
    hdcoord.continuousAt.eventually (isOpen_compl_singleton.mem_nhds hi)
  have heq : (fun x : Phase => (gauge B x)⁻¹) =ᶠ[nhds u] (fun x => G x i / x i) := by
    filter_upwards [hne] with x hx
    simp [G, hx]
  exact hratio.congr_of_eventuallyEq heq

/-- Convex-model specialization: the radial chart supplies the full tangent
transport. No sphere-tangent lift or differential compatibility is assumed.
Boundary contact positivity is still explicit. -/
private theorem convex_model_sphere_reeb_transport {μ c : ℝ} (M : ConvexRegularizationModel μ c)
    (hcontact : ∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))
    (u : Phase) (hu : u ∈ unitThreeSphere) :
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
      fderiv ℝ G u R = (phaseRadialContact y X)⁻¹ • X := by
  have hsmooth : ∀ y ∈ frontier M.body, ContDiffAt ℝ ∞ M.modelHamiltonian y := by
    intro y hy
    have htarget : y ∈ M.target := by
      rw [← M.image_frontier] at hy
      obtain ⟨s, hs, rfl⟩ := hy
      exact M.toModel_mapsTo (M.contains_component hs)
    exact M.model_smooth.contDiffAt (M.target_open.mem_nhds htarget)
  have hrad : ∀ y ∈ frontier M.body, fderiv ℝ M.modelHamiltonian y y ≠ 0 := by
    intro y hy
    have h := (hamiltonian_radial_characteristic_normalization M.modelHamiltonian y
      (hcontact y hy)).2.2.2
    have hp := hcontact y hy
    intro heq
    rw [heq] at h
    norm_num at h
    rw [h] at hp
    exact lt_irrefl _ hp
  have h0 := mem_interior_iff_mem_nhds.mp M.origin_interior
  have hb := M.body_compact.isVonNBounded ℝ
  have hchart := smooth_radial_gauge_chart M.body M.body_convex h0 hb
    M.modelHamiltonian M.model_zero hsmooth hrad
  let a : Phase → ℝ := fun x => (gauge M.body x)⁻¹
  let G : Phase → Phase := fun x => a x • x
  let y := G u
  let X := hamiltonianVectorField M.modelHamiltonian y
  have hy : y ∈ frontier M.body := (hchart.2 u hu).2.1
  have hune : u ≠ 0 := by
    intro h
    have hQ : zNormSq u + wNormSq u = 1 := hu
    simp [h, zNormSq, wNormSq] at hQ
  have hapos : 0 < a u := inv_pos.mpr ((gauge_pos (absorbent_nhds_zero h0) hb).2 hune)
  have ha : DifferentiableAt ℝ a u := gauge_inverse_scale_differentiable M.body u hune
    ((hchart.2 u hu).1.differentiableAt (by simp))
  have hF := (hsmooth y hy).differentiableAt (by simp)
  have hFG : (fun x : Phase => M.modelHamiltonian (a x • x)) =ᶠ[nhds u]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hune] with x hx
    exact M.model_zero _ (gauge_inverse_frontier M.body M.body_convex h0 hb x hx)
  have hrad_u : fderiv ℝ M.modelHamiltonian y u ≠ 0 := by
    intro hz
    apply hrad y hy
    change fderiv ℝ M.modelHamiltonian y (a u • u) = 0
    simp [hz]
  have hp := hcontact y hy
  have hn := hamiltonian_radial_characteristic_normalization M.modelHamiltonian y hp
  have hX : fderiv ℝ M.modelHamiltonian y X = 0 := by
    have hnorm := hn.2.1
    rw [map_smul, smul_eq_mul] at hnorm
    exact (mul_eq_zero.mp hnorm).resolve_left (inv_ne_zero (ne_of_gt hp))
  have hlift := radial_boundary_tangent_lift a M.modelHamiltonian u X hu ha hapos hF hFG
    hrad_u hX
  let T := (a u)⁻¹ • X -
    ((a u)⁻¹ * (u 0 * X 0 + u 1 * X 1 + u 2 * X 2 + u 3 * X 3)) • u
  let R := (phaseRadialContact y X)⁻¹ • T
  have hreeb := radial_hamiltonian_reeb_transport a M.modelHamiltonian u T ha hlift.1
    hlift.2.1 (fun w _ => hlift.2.2 w) hp
  refine ⟨R, hreeb.1, hreeb.2.1, hreeb.2.2, ?_⟩
  change fderiv ℝ G u ((phaseRadialContact y X)⁻¹ • T) = _
  rw [map_smul, hlift.2.1]

theorem solution {μ c : ℝ} (M : ConvexRegularizationModel μ c)
    (u : Phase) (hu : u ∈ unitThreeSphere) :
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
      fderiv ℝ G u R = (phaseRadialContact y X)⁻¹ • X := by
  exact convex_model_sphere_reeb_transport M
    (BirkhoffGlobalSection.convex_model_boundary_contact_positive M) u hu
