-- Prove2me | solution 1 for BirkhoffGlobalSection.radial_characteristic_bundle
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T12:48:58.962676+00:00
-- url     : https://prove2.me/submissions/a276b45a-b2a0-42bf-aa1d-923f4fcf421c

import Theorems.Thm_BirkhoffGlobalSection_convex_model_boundary_contact_positive
import Theorems.Thm_BirkhoffGlobalSection_weighted_radial_contact_exterior_derivative
import Theorems.Thm_BirkhoffGlobalSection_radial_rescaling_contact_pullback
import Theorems.Thm_BirkhoffGlobalSection_hamiltonian_radial_characteristic_normalization
import Theorems.Thm_BirkhoffGlobalSection_smooth_radial_gauge_chart
import Theorems.Thm_ConvexAnalysis_radial_derivative_pos_of_inward_negative
import Definitions.Def_BirkhoffGlobalSection_ContactVariationalInterfaces
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false



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

private theorem radial_pairing_coordinate_expansion (L : Phase →L[ℝ] ℝ) (v : Phase) :
    L v = v 0 * L (coordinateVector 0) + v 1 * L (coordinateVector 1) +
      v 2 * L (coordinateVector 2) + v 3 * L (coordinateVector 3) := by
  have hv : v = v 0 • coordinateVector 0 + v 1 • coordinateVector 1 +
      v 2 • coordinateVector 2 + v 3 • coordinateVector 3 := by
    ext i
    fin_cases i <;> simp [coordinateVector]
  calc
    L v = L (v 0 • coordinateVector 0 + v 1 • coordinateVector 1 +
      v 2 • coordinateVector 2 + v 3 • coordinateVector 3) := congrArg L hv
    _ = _ := by simp

private theorem hamiltonian_radial_contact_pairing (F : Phase → ℝ) (y : Phase) :
    phaseRadialContact y (hamiltonianVectorField F y) = fderiv ℝ F y y / 2 := by
  rw [radial_pairing_coordinate_expansion (fderiv ℝ F y) y]
  simp [phaseRadialContact, phaseSymplecticForm, hamiltonianVectorField, partialDerivative]
  ring

private theorem convex_model_contact_positive_of_inward_negative {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    (hneg : ∀ y ∈ frontier M.body, ∀ t : ℝ, 0 ≤ t → t < 1 →
      M.modelHamiltonian (t • y) < 0) :
    ∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y) := by
  intro y hy
  have hyne : y ≠ 0 := by
    intro heq
    have hn := hy.2
    apply hn
    simpa only [heq] using M.origin_interior
  have hrad := ConvexAnalysis.radial_derivative_pos_of_inward_negative
    M.modelHamiltonian y hyne (M.model_hessian.1 y hy) (M.model_zero y hy)
    (hneg y hy) (M.model_hessian.2 y hy)
  rw [hamiltonian_radial_contact_pairing]
  exact div_pos hrad (by norm_num)

private theorem local_inward_negative_derivative_nonnegative (f : ℝ → ℝ) (d ε : ℝ)
    (hε : 0 < ε) (hd : HasDerivAt f d 1) (hzero : f 1 = 0)
    (hneg : ∀ t : ℝ, 1 - ε ≤ t → t < 1 → f t < 0) : 0 ≤ d := by
  have hmax : IsMaxOn f (Set.Icc (1 - ε) 1) 1 := by
    intro t ht
    change f t ≤ f 1
    rcases ht.2.eq_or_lt with he | hlt
    · rw [he]
    · rw [hzero]
      exact (hneg t ht.1 hlt).le
  have hseg : segment ℝ (1 : ℝ) (1 - ε) ⊆ Set.Icc (1 - ε) 1 :=
    (convex_Icc _ _).segment_subset ⟨by linarith, le_rfl⟩ ⟨le_rfl, by linarith⟩
  have h := hmax.localize.hasFDerivWithinAt_nonpos
    hd.hasFDerivAt.hasFDerivWithinAt (sub_mem_posTangentConeAt_of_segment_subset hseg)
  have hmul : d * (-ε) ≤ 0 := by simpa [mul_comm] using h
  nlinarith

private theorem local_inward_negative_not_stationary (f : ℝ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hc : ContinuousAt f 1) (hzero : f 1 = 0)
    (hneg : ∀ t : ℝ, 1 - ε ≤ t → t < 1 → f t < 0)
    (hsecond : 0 < deriv (deriv f) 1) : deriv f 1 ≠ 0 := by
  intro hstationary
  have hmin := isLocalMin_of_deriv_deriv_pos hsecond hstationary hc
  obtain ⟨η, hη, hnear⟩ := Metric.eventually_nhds_iff.mp hmin
  let δ : ℝ := min (η / 2) (ε / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδε : δ ≤ ε / 2 := min_le_right _ _
  have hδη : δ < η := (min_le_left _ _).trans_lt (by linarith)
  have hd : dist (1 - δ) (1 : ℝ) < η := by
    rw [Real.dist_eq]
    have heq : (1 - δ) - 1 = -δ := by ring
    rw [heq, abs_neg, abs_of_pos hδ]
    exact hδη
  have hl := hnear hd
  have hn := hneg (1 - δ) (by linarith) (by linarith)
  rw [hzero] at hl
  linarith

private theorem local_radial_slice_derivatives {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ) (s : E)
    (hc : ContDiffAt ℝ 2 F s) :
    let f : ℝ → ℝ := fun t => F (t • s)
    deriv f 1 = fderiv ℝ F s s ∧
      deriv (deriv f) 1 = fderiv ℝ (fun x => fderiv ℝ F x s) s s := by
  let P : ℝ → E := fun t => t • s
  let f : ℝ → ℝ := F ∘ P
  let G : E → ℝ := fun x => fderiv ℝ F x s
  have hP (t : ℝ) : HasDerivAt P s t := by
    simpa only [P, id_eq, one_smul] using (hasDerivAt_id t).smul_const s
  have hPc : Continuous P := continuous_id.smul continuous_const
  have hP1 : P 1 = s := one_smul ℝ s
  have hf : HasDerivAt f (fderiv ℝ F s s) 1 :=
    (hc.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 1 (hP 1) hP1.symm
  have hGc : ContDiffAt ℝ 1 G s :=
    (hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have hg : HasDerivAt (G ∘ P) (fderiv ℝ G s s) 1 :=
    hGc.differentiableAt_one.hasFDerivAt.comp_hasDerivAt_of_eq 1 (hP 1) hP1.symm
  have hPt : Filter.Tendsto P (nhds 1) (nhds s) := by
    simpa only [hP1] using hPc.continuousAt.tendsto (x := 1)
  have heq : deriv f =ᶠ[nhds 1] G ∘ P := by
    filter_upwards [hPt.eventually (hc.eventually (by norm_num))] with t ht
    exact (ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hP t) |>.deriv
  exact ⟨hf.deriv, (hg.congr_of_eventuallyEq heq).deriv⟩

private theorem radial_derivative_pos_of_local_inward_negative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ) (s : E)
    (hsne : s ≠ 0) (hc : ContDiffAt ℝ 2 F s) (hzero : F s = 0)
    (hneg : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 1 - ε ≤ t → t < 1 → F (t • s) < 0)
    (hcurv : ∀ v : E, v ≠ 0 → fderiv ℝ F s v = 0 →
      0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v) :
    0 < fderiv ℝ F s s := by
  obtain ⟨ε, hε, hneg⟩ := hneg
  let f : ℝ → ℝ := fun t => F (t • s)
  obtain ⟨hfirst, hsecond⟩ := local_radial_slice_derivatives F s hc
  have hP : HasDerivAt (fun t : ℝ => t • s) s 1 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (1 : ℝ)).smul_const s
  have hf : HasDerivAt f (fderiv ℝ F s s) 1 :=
    (hc.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 1 hP
      (one_smul ℝ s).symm
  have hfzero : f 1 = 0 := by simpa [f] using hzero
  have hnonneg := local_inward_negative_derivative_nonnegative f _ ε hε hf hfzero hneg
  have hne : fderiv ℝ F s s ≠ 0 := by
    intro hstationary
    have hpositive : 0 < deriv (deriv f) 1 := by
      rw [hsecond]
      exact hcurv s hsne hstationary
    have hnot := local_inward_negative_not_stationary f ε hε
      hf.continuousAt hfzero hneg hpositive
    rw [hfirst, hstationary] at hnot
    exact hnot rfl
  exact lt_of_le_of_ne hnonneg hne.symm

private theorem convex_model_contact_positive_of_local_inward_negative {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    (hneg : ∀ y ∈ frontier M.body, ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, 1 - ε ≤ t → t < 1 → M.modelHamiltonian (t • y) < 0) :
    ∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y) := by
  intro y hy
  have hyne : y ≠ 0 := by
    intro heq
    exact hy.2 (heq ▸ M.origin_interior)
  have hrad := radial_derivative_pos_of_local_inward_negative M.modelHamiltonian y
    hyne (M.model_hessian.1 y hy) (M.model_zero y hy) (hneg y hy) (M.model_hessian.2 y hy)
  rw [hamiltonian_radial_contact_pairing]
  exact div_pos hrad (by norm_num)

private theorem local_inward_negative_of_radial_derivative_pos {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ) (s : E)
    (hc : DifferentiableAt ℝ F s) (hzero : F s = 0)
    (hrad : 0 < fderiv ℝ F s s) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 1 - ε ≤ t → t < 1 → F (t • s) < 0 := by
  let f : ℝ → ℝ := fun t => F (t • s)
  have hP : HasDerivAt (fun t : ℝ => t • s) s 1 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (1 : ℝ)).smul_const s
  have hf : HasDerivAt f (fderiv ℝ F s s) 1 :=
    hc.hasFDerivAt.comp_hasDerivAt_of_eq 1 hP (one_smul ℝ s).symm
  have hfzero : f 1 = 0 := by simpa [f] using hzero
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos
    (by simpa only [hf.deriv] using hrad) hfzero
  obtain ⟨η, hη, hnear⟩ := Metric.eventually_nhds_iff.mp hsign
  refine ⟨η / 2, by linarith, ?_⟩
  intro t ht ht1
  have hd : dist t (1 : ℝ) < η := by
    rw [Real.dist_eq, abs_of_neg (by linarith : t - 1 < 0)]
    linarith
  have he := hnear hd
  rw [sign_neg (sub_neg.mpr ht1)] at he
  exact sign_eq_neg_one_iff.mp he

private theorem convex_model_contact_positive_iff_local_inward_negative {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) :
    (∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y)) ↔
    (∀ y ∈ frontier M.body, ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, 1 - ε ≤ t → t < 1 → M.modelHamiltonian (t • y) < 0) := by
  constructor
  · intro hpos y hy
    apply local_inward_negative_of_radial_derivative_pos M.modelHamiltonian y
      ((M.model_hessian.1 y hy).differentiableAt (by norm_num)) (M.model_zero y hy)
    have h := hpos y hy
    rw [hamiltonian_radial_contact_pairing] at h
    linarith
  · exact convex_model_contact_positive_of_local_inward_negative M

private theorem convex_radial_slice_mem_interior {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E) (hK : Convex ℝ K)
    (h0 : (0 : E) ∈ interior K) (y : E) (hy : y ∈ closure K)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) : t • y ∈ interior K := by
  have h := hK.add_smul_sub_mem_interior' hy h0
    (show 1 - t ∈ Set.Ioc (0 : ℝ) 1 from ⟨by linarith, by linarith⟩)
  convert h using 1
  simp only [zero_sub, smul_neg, sub_smul, one_smul]
  abel

private theorem convex_model_contact_positive_of_local_interior_negative {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    (hneg : ∀ y ∈ frontier M.body, ∀ᶠ x in nhds y,
      x ∈ interior M.body → M.modelHamiltonian x < 0) :
    ∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y) := by
  apply convex_model_contact_positive_of_local_inward_negative M
  intro y hy
  have hP : Filter.Tendsto (fun t : ℝ => t • y) (nhds 1) (nhds y) := by
    have hp : Continuous (fun t : ℝ => t • y) := continuous_id.smul continuous_const
    simpa only [one_smul] using hp.continuousAt.tendsto (x := (1 : ℝ))
  obtain ⟨η, hη, hnear⟩ := Metric.eventually_nhds_iff.mp (hP.eventually (hneg y hy))
  let ε : ℝ := min (η / 2) (1 / 2)
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  refine ⟨ε, hε, ?_⟩
  intro t ht ht1
  have heη : ε ≤ η / 2 := min_le_left _ _
  have he1 : ε ≤ 1 / 2 := min_le_right _ _
  have hd : dist t (1 : ℝ) < η := by
    rw [Real.dist_eq, abs_of_neg (by linarith : t - 1 < 0)]
    linarith
  exact hnear hd (convex_radial_slice_mem_interior M.body M.body_convex
    M.origin_interior y hy.1 t (by linarith) ht1)

theorem solution :
(∀ (a : Phase → ℝ) (u v w : Phase)
    (ha : DifferentiableAt ℝ a u),
    fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x w) u v -
      fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x v) u w =
    -phaseSymplecticForm
      (fderiv ℝ (fun x : Phase => a x • x) u v)
      (fderiv ℝ (fun x : Phase => a x • x) u w)) ∧
(∀ (a F : Phase → ℝ) (u T : Phase)
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
          fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x R) u w = 0)) ∧
(∀ (a F : Phase → ℝ) (u X : Phase)
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
        (fderiv ℝ (fun x : Phase => a x • x) u w) = 0)) ∧
(∀ {μ c : ℝ} (M : ConvexRegularizationModel μ c)
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
      fderiv ℝ G u R = (phaseRadialContact y X)⁻¹ • X) ∧
(∀ (F : Phase → ℝ) (y : Phase),
    phaseRadialContact y (hamiltonianVectorField F y) = fderiv ℝ F y y / 2) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    (hneg : ∀ y ∈ frontier M.body, ∀ t : ℝ, 0 ≤ t → t < 1 →
      M.modelHamiltonian (t • y) < 0),
    ∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y)) ∧
(∀ (f : ℝ → ℝ) (d ε : ℝ)
    (hε : 0 < ε) (hd : HasDerivAt f d 1) (hzero : f 1 = 0)
    (hneg : ∀ t : ℝ, 1 - ε ≤ t → t < 1 → f t < 0),
    0 ≤ d) ∧
(∀ {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ) (s : E)
    (hsne : s ≠ 0) (hc : ContDiffAt ℝ 2 F s) (hzero : F s = 0)
    (hneg : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 1 - ε ≤ t → t < 1 → F (t • s) < 0)
    (hcurv : ∀ v : E, v ≠ 0 → fderiv ℝ F s v = 0 →
      0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v),
    0 < fderiv ℝ F s s) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    (hneg : ∀ y ∈ frontier M.body, ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, 1 - ε ≤ t → t < 1 → M.modelHamiltonian (t • y) < 0),
    ∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y)) ∧
(∀ {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ) (s : E)
    (hc : DifferentiableAt ℝ F s) (hzero : F s = 0)
    (hrad : 0 < fderiv ℝ F s s),
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 1 - ε ≤ t → t < 1 → F (t • s) < 0) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c),
    (∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y)) ↔
    (∀ y ∈ frontier M.body, ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, 1 - ε ≤ t → t < 1 → M.modelHamiltonian (t • y) < 0)) ∧
(∀ {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E) (hK : Convex ℝ K)
    (h0 : (0 : E) ∈ interior K) (y : E) (hy : y ∈ closure K)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1),
    t • y ∈ interior K) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    (hneg : ∀ y ∈ frontier M.body, ∀ᶠ x in nhds y,
      x ∈ interior M.body → M.modelHamiltonian x < 0),
    ∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y)) := by
  exact ⟨@radial_contact_exterior_pullback, ⟨@radial_hamiltonian_reeb_transport, ⟨@radial_boundary_tangent_lift, ⟨@convex_model_sphere_reeb_transport, ⟨@hamiltonian_radial_contact_pairing, ⟨@convex_model_contact_positive_of_inward_negative, ⟨@local_inward_negative_derivative_nonnegative, ⟨@radial_derivative_pos_of_local_inward_negative, ⟨@convex_model_contact_positive_of_local_inward_negative, ⟨@local_inward_negative_of_radial_derivative_pos, ⟨@convex_model_contact_positive_iff_local_inward_negative, ⟨@convex_radial_slice_mem_interior, @convex_model_contact_positive_of_local_interior_negative⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
