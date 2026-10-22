-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_complete_sphere_reeb_flow
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T08:22:18.814063+00:00
-- url     : https://prove2.me/submissions/b896f82d-a97d-456d-b34b-840db3d23e7e

import Theorems.Thm_BirkhoffGlobalSection_convex_model_complete_normalized_flow_of_model_fields
import Theorems.Thm_BirkhoffGlobalSection_convex_model_sphere_reeb_transport_of_model_fields
import Theorems.Thm_BirkhoffGlobalSection_convex_model_smooth_radial_chart
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

open BirkhoffGlobalSection Set
open scoped Topology ContDiff

private theorem sphere_curve_tangent (q : ℝ → Phase) (v : Phase) (t : ℝ)
    (hq : ∀ s, q s ∈ unitThreeSphere) (hd : HasDerivAt q v t) :
    q t 0 * v 0 + q t 1 * v 1 + q t 2 * v 2 + q t 3 * v 3 = 0 := by
  have hc (i : Fin 4) : HasDerivAt (fun s => q s i) (v i) t :=
    (ContinuousLinearMap.proj i : Phase →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hd
  have hsq (i : Fin 4) : HasDerivAt (fun s => q s i * q s i)
      (v i * q t i + q t i * v i) t := HasDerivAt.mul (hc i) (hc i)
  have hsum := HasDerivAt.add (HasDerivAt.add (hsq 0) (hsq 1))
    (HasDerivAt.add (hsq 2) (hsq 3))
  have heq : (fun s => q s 0 * q s 0 + q s 1 * q s 1 +
      (q s 2 * q s 2 + q s 3 * q s 3)) = fun _ => (1 : ℝ) := by
    funext s
    have h := hq s
    change zNormSq (q s) + wNormSq (q s) = 1 at h
    simpa [zNormSq, wNormSq, pow_two] using h
  have hz := hsum.unique ((hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun s => congrFun heq s)))
  nlinarith

private theorem radial_derivative_tangent_injective (a : Phase → ℝ) (u v : Phase)
    (hu : u ∈ unitThreeSphere) (ha : DifferentiableAt ℝ a u) (hapos : 0 < a u)
    (hv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0)
    (hz : fderiv ℝ (fun x => a x • x) u v = 0) : v = 0 := by
  have hd : fderiv ℝ (fun x => a x • x) u v =
      (fderiv ℝ a u v) • u + a u • v := by
    rw [fderiv_fun_smul ha (show DifferentiableAt ℝ (fun x : Phase => x) u from differentiableAt_id)]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, fderiv_fun_id, ContinuousLinearMap.id_apply]
    exact add_comm _ _
  have hcoord (i : Fin 4) : (fderiv ℝ a u v) * u i + a u * v i = 0 := by
    have h := congrFun (hd.symm.trans hz) i
    simpa using h
  have hunit : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 = 1 := by
    simpa [unitThreeSphere, zNormSq, wNormSq, add_assoc] using hu
  have hda : fderiv ℝ a u v = 0 := by
    have hsum : (fderiv ℝ a u v) *
        (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2) +
        a u * (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3) = 0 := by
      calc
        _ = u 0 * ((fderiv ℝ a u v) * u 0 + a u * v 0) +
            u 1 * ((fderiv ℝ a u v) * u 1 + a u * v 1) +
            u 2 * ((fderiv ℝ a u v) * u 2 + a u * v 2) +
            u 3 * ((fderiv ℝ a u v) * u 3 + a u * v 3) := by ring
        _ = 0 := by simp only [hcoord, mul_zero, add_zero]
    simpa only [hunit, hv, mul_one, mul_zero, add_zero] using hsum
  ext i
  have h := hcoord i
  rw [hda, zero_mul, zero_add] at h
  exact (mul_eq_zero.mp h).resolve_left (ne_of_gt hapos)

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

private theorem convex_model_radial_state_homeomorph {μ c : ℝ} (M : ConvexRegularizationModel μ c) :
    ∃ e : {u : Phase // u ∈ unitThreeSphere} ≃ₜ ConvexModelState M,
      (∀ u, (e u : Phase) = (gauge M.body (u : Phase))⁻¹ • (u : Phase)) ∧
      (∀ y, (e.symm y : Phase) = radialNormalize (y : Phase)) := by
  have hc := convex_model_smooth_radial_chart M
  let e : {u : Phase // u ∈ unitThreeSphere} ≃ₜ ConvexModelState M := {
    toFun := fun u => ⟨(gauge M.body (u : Phase))⁻¹ • (u : Phase), (hc.2 u u.property).2.1⟩
    invFun := fun y => ⟨radialNormalize (y : Phase), (hc.1 y y.property).2.1⟩
    left_inv := fun u => Subtype.ext ((hc.2 u u.property).2.2)
    right_inv := fun y => Subtype.ext ((hc.1 y y.property).2.2)
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply continuous_iff_continuousAt.mpr
      intro u
      exact (hc.2 u u.property).1.continuousAt.comp continuous_subtype_val.continuousAt
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply continuous_iff_continuousAt.mpr
      intro y
      exact (hc.1 y y.property).1.continuousAt.comp continuous_subtype_val.continuousAt }
  exact ⟨e, fun _ => rfl, fun _ => rfl⟩

theorem solution {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    {φ : Flow ℝ (LeftEnergyState μ c)} (D : ConvexModelDynamics M φ) :
    let a : Phase → ℝ := fun x => (gauge M.body x)⁻¹
    ∃ e : {u : Phase // u ∈ unitThreeSphere} ≃ₜ ConvexModelState M,
      ∃ ψ : Flow ℝ (ConvexModelState M),
        ∃ θ : Flow ℝ {u : Phase // u ∈ unitThreeSphere},
          ∃ R : {u : Phase // u ∈ unitThreeSphere} → Phase,
            (∀ u, (e u : Phase) = a u • (u : Phase)) ∧
            (∀ y, (e.symm y : Phase) = radialNormalize (y : Phase)) ∧
            (∀ t u, e (θ t u) = ψ t (e u)) ∧
            (∀ s t, HasDerivAt (fun v => (ψ v s : Phase))
              ((phaseRadialContact (ψ t s)
                (hamiltonianVectorField M.modelHamiltonian (ψ t s)))⁻¹ •
                  hamiltonianVectorField M.modelHamiltonian (ψ t s)) t) ∧
            (∀ u,
              (u.val 0 * R u 0 + u.val 1 * R u 1 + u.val 2 * R u 2 + u.val 3 * R u 3 = 0) ∧
              (a u)^2 * phaseRadialContact u (R u) = 1 ∧
              (∀ w : Phase,
                u.val 0 * w 0 + u.val 1 * w 1 + u.val 2 * w 2 + u.val 3 * w 3 = 0 →
                fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x w) u (R u) -
                  fderiv ℝ (fun x => (a x)^2 * phaseRadialContact x (R u)) u w = 0)) ∧
            (∀ u t, HasDerivAt (fun v => (θ v u : Phase)) (R (θ t u)) t) := by
  dsimp only
  let a : Phase → ℝ := fun x => (gauge M.body x)⁻¹
  let G : Phase → Phase := fun x => a x • x
  have hc := convex_model_smooth_radial_chart M
  obtain ⟨e, he, hi⟩ := convex_model_radial_state_homeomorph M
  obtain ⟨ψ, hψ⟩ := convex_model_complete_normalized_flow_of_model_fields M D
  let θ : Flow ℝ {u : Phase // u ∈ unitThreeSphere} := {
    toFun := fun t u => e.symm (ψ t (e u))
    cont' := e.symm.continuous.comp
      (ψ.continuous continuous_fst (e.continuous.comp continuous_snd))
    map_add' := by intro t s u; simp only [ψ.map_add, e.apply_symm_apply]
    map_zero' := by intro u; simp only [ψ.map_zero_apply, e.symm_apply_apply] }
  have hconj (t : ℝ) (u : {u : Phase // u ∈ unitThreeSphere}) :
      e (θ t u) = ψ t (e u) := e.apply_symm_apply _
  let V : ConvexModelState M → Phase := fun y =>
    (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
      hamiltonianVectorField M.modelHamiltonian y
  let R : {u : Phase // u ∈ unitThreeSphere} → Phase := fun u =>
    fderiv ℝ radialNormalize (e u) (V (e u))
  have hθ (u : {u : Phase // u ∈ unitThreeSphere}) (t : ℝ) :
      HasDerivAt (fun v => (θ v u : Phase)) (R (θ t u)) t := by
    have h := ((hc.1 (ψ t (e u)) (ψ t (e u)).property).1.differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t (hψ (e u) t)
    have h' := h.congr_of_eventuallyEq
      (f₁ := fun v => (θ v u : Phase))
      (Filter.Eventually.of_forall (fun v => hi (ψ v (e u))))
    simpa only [R, V, hconj] using h'
  have ht (u : {u : Phase // u ∈ unitThreeSphere}) :
      u.val 0 * R u 0 + u.val 1 * R u 1 + u.val 2 * R u 2 + u.val 3 * R u 3 = 0 := by
    have h := sphere_curve_tangent (fun t => (θ t u : Phase)) (R u) 0
      (fun t => (θ t u).property) (by simpa only [θ.map_zero_apply] using hθ u 0)
    simpa only [θ.map_zero_apply] using h
  have hmap (u : {u : Phase // u ∈ unitThreeSphere}) :
      fderiv ℝ G u (R u) = V (e u) := by
    have hG : HasFDerivAt G (fderiv ℝ G u) (θ 0 u : Phase) := by
      simpa only [θ.map_zero_apply] using
        ((hc.2 u u.property).1.differentiableAt (by simp)).hasFDerivAt
    have h := hG.comp_hasDerivAt 0
      (show HasDerivAt (fun t => (θ t u : Phase)) (R u) 0 by
        simpa only [θ.map_zero_apply] using hθ u 0)
    have heq (t : ℝ) : G (θ t u) = (ψ t (e u) : Phase) := by
      rw [← hconj, he]
    have h' := h.congr_of_eventuallyEq
      (f₁ := fun t => (ψ t (e u) : Phase))
      (Filter.Eventually.of_forall (fun t => (heq t).symm))
    exact h'.unique (by simpa only [ψ.map_zero_apply] using hψ (e u) 0)
  refine ⟨e, ψ, θ, R, he, hi, hconj, hψ, ?_, hθ⟩
  intro u
  obtain ⟨S, hSt, hSα, hSd, hSG⟩ := convex_model_sphere_reeb_transport_of_model_fields M u u.property
  have hune : (u : Phase) ≠ 0 := by
    intro hz
    have h := u.property
    simp [unitThreeSphere, hz, zNormSq, wNormSq] at h
  have hapos : 0 < a u := inv_pos.mpr ((gauge_pos
    (absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp M.origin_interior))
    (M.body_compact.isVonNBounded ℝ)).2 hune)
  have ha : DifferentiableAt ℝ a u := gauge_inverse_scale_differentiable M.body u hune
    ((hc.2 u u.property).1.differentiableAt (by simp))
  have hdiff : R u - S = 0 := by
    apply radial_derivative_tangent_injective a u (R u - S) u.property ha hapos
    · simp only [Pi.sub_apply]
      linarith [ht u, hSt]
    · rw [map_sub, hmap]
      have hS : fderiv ℝ G u S = V (e u) := by
        simpa only [V, he] using hSG
      rw [hS, sub_self]
  have hRS : R u = S := sub_eq_zero.mp hdiff
  exact ⟨ht u, by simpa only [hRS] using hSα, by simpa only [hRS] using hSd⟩
