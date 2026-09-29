-- Prove2me | solution 1 for DynamicsRelativity.kepler_energy_eccentricity_planar
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T09:05:52.583605+00:00
-- url     : https://prove2.me/submissions/743c9399-6772-43e2-97e3-0c2cbb48cca1

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity


noncomputable def W8_DynamicsRelativity_crossLin : Vec →ₗ[ℝ] Vec →ₗ[ℝ] Vec :=
  LinearMap.mk₂ ℝ cross
    (fun a b c => by unfold cross; ext i; simp [map_add, LinearMap.add_apply])
    (fun r a b => by unfold cross; ext i; simp [map_smul, LinearMap.smul_apply])
    (fun a b c => by unfold cross; ext i; simp [map_add])
    (fun r a b => by unfold cross; ext i; simp [map_smul])

noncomputable def W8_DynamicsRelativity_B : Vec →L[ℝ] Vec →L[ℝ] Vec :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Vec →ₗ[ℝ] Vec) ≃ₗ[ℝ] (Vec →L[ℝ] Vec)).toLinearMap ∘ₗ W8_DynamicsRelativity_crossLin)

lemma W8_DynamicsRelativity_B_apply (a b : Vec) : W8_DynamicsRelativity_B a b = cross a b := by
  simp [W8_DynamicsRelativity_B, W8_DynamicsRelativity_crossLin]

lemma W8_DynamicsRelativity_cross_self' (a : Vec) : cross a a = 0 := by
  unfold cross; simp [cross_self]

lemma W8_DynamicsRelativity_hasDerivAt_L {m : ℝ} {F : ℝ → ℝ} {x : ℝ → Vec} (h : CentralForceMotion m F x) (t : ℝ) :
    HasDerivAt (angularMomentum m x) (m • cross (x t) (acc x t)) t := by
  have hx1 : Differentiable ℝ x := h.smooth.differentiable (by norm_num)
  have hv1 : Differentiable ℝ (vel x) := by
    have : ContDiff ℝ 1 (deriv x) := h.smooth.iterate_deriv' 1 1
    exact this.differentiable (by norm_num)
  have hxd : HasDerivAt x (vel x t) t := (hx1 t).hasDerivAt
  have hvd : HasDerivAt (vel x) (acc x t) t := (hv1 t).hasDerivAt
  have hB := ContinuousLinearMap.hasDerivAt_of_bilinear (B := W8_DynamicsRelativity_B) (fun _ => hxd) (fun _ => hvd)
  have hfun : angularMomentum m x = fun s => m • W8_DynamicsRelativity_B (x s) (vel x s) := by
    funext s; simp [angularMomentum, W8_DynamicsRelativity_B_apply]
  rw [hfun]
  have := hB.const_smul m
  refine this.congr_deriv ?_
  rw [W8_DynamicsRelativity_B_apply, W8_DynamicsRelativity_B_apply, W8_DynamicsRelativity_cross_self', add_zero]


lemma W8_DynamicsRelativity_L_const {m : ℝ} {F : ℝ → ℝ} {x : ℝ → Vec} (h : CentralForceMotion m F x) (t₀ t₁ : ℝ) :
    angularMomentum m x t₀ = angularMomentum m x t₁ := by
  have hm := h.mass_pos
  have hzero : ∀ t, cross (x t) (acc x t) = 0 := by
    intro t
    have ha : acc x t = (m⁻¹ * (F ‖x t‖ / ‖x t‖)) • x t := by
      have := h.eom t
      rw [mul_smul, ← this, smul_smul, inv_mul_cancel₀ hm.ne', one_smul]
    rw [ha]; unfold cross; simp [WithLp.ofLp_smul, map_smul, cross_self]
  have hd : ∀ t, HasDerivAt (angularMomentum m x) 0 t := by
    intro t
    have := W8_DynamicsRelativity_hasDerivAt_L h t
    rw [hzero, smul_zero] at this
    exact this
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t₀ t₁

lemma W8_DynamicsRelativity_triple (a b c : Vec) : cross a (cross b c) = (inner ℝ a c) • b - (inner ℝ a b) • c := by
  unfold cross
  ext i; fin_cases i <;> simp [cross_apply, PiLp.inner_apply, Fin.sum_univ_three] <;> ring

lemma W8_DynamicsRelativity_scalar_triple (x v : Vec) : inner ℝ (cross v (cross x v)) x = ‖cross x v‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold cross
  simp [cross_apply, PiLp.inner_apply, Fin.sum_univ_three]; ring

lemma W8_DynamicsRelativity_cross_smul_left' (s : ℝ) (a b : Vec) : cross (s • a) b = s • cross a b := by
  unfold cross
  ext i; fin_cases i <;> simp [cross_apply]

lemma W8_DynamicsRelativity_conic_main {k m : ℝ} {x : ℝ → Vec} (hk : 0 < k) (h : KeplerMotion k m x) :
    ∀ t, ‖x t‖ + inner ℝ (k⁻¹ • cross (vel x 0) (cross (x 0) (vel x 0)) - ‖x 0‖⁻¹ • x 0) (x t)
      = ‖cross (x 0) (vel x 0)‖ ^ 2 / k := by
  have hm := h.mass_pos
  have hx1 : Differentiable ℝ x := h.smooth.differentiable (by norm_num)
  have hv1 : Differentiable ℝ (vel x) := by
    have : ContDiff ℝ 1 (deriv x) := h.smooth.iterate_deriv' 1 1
    exact this.differentiable (by norm_num)
  set hc := cross (x 0) (vel x 0) with hhc
  have hct : ∀ t, cross (x t) (vel x t) = hc := by
    intro t
    have := W8_DynamicsRelativity_L_const h t 0
    unfold angularMomentum at this
    exact smul_right_injective _ hm.ne' this
  let A : ℝ → Vec := fun t => k⁻¹ • cross (vel x t) hc - (‖x t‖⁻¹) • x t
  have hA : ∀ t, HasDerivAt A 0 t := by
    intro t
    have hr : 0 < ‖x t‖ := norm_pos_iff.mpr (h.ne_origin t)
    have hxd : HasDerivAt x (vel x t) t := (hx1 t).hasDerivAt
    have hvd : HasDerivAt (vel x) (acc x t) t := (hv1 t).hasDerivAt
    have hx2 : HasDerivAt (fun s => ‖x s‖ ^ 2) (2 * inner ℝ (x t) (vel x t)) t := hxd.norm_sq
    have hn : HasDerivAt (fun s => ‖x s‖) (2 * inner ℝ (x t) (vel x t) / (2 * ‖x t‖)) t := by
      have := hx2.sqrt (by positivity)
      simp only [Real.sqrt_sq (norm_nonneg _)] at this
      convert this using 2
    have hinv := hn.inv hr.ne'
    have hcr : HasDerivAt (fun s => cross (vel x s) hc) (cross (acc x t) hc) t := by
      have := (W8_DynamicsRelativity_B.flip hc).hasFDerivAt.comp_hasDerivAt t hvd
      simp only [Function.comp_def, ContinuousLinearMap.flip_apply, W8_DynamicsRelativity_B_apply] at this
      exact this
    have hAd := (hcr.const_smul k⁻¹).sub (hinv.smul hxd)
    refine hAd.congr_deriv ?_
    have ha : acc x t = (-k / ‖x t‖ ^ 3) • x t := by
      have := h.eom t
      simp only [keplerForce] at this
      rw [← inv_smul_smul₀ hm.ne' (acc x t), this, smul_smul]
      congr 1
      field_simp
    rw [ha, ← hct t, W8_DynamicsRelativity_cross_smul_left', W8_DynamicsRelativity_triple, real_inner_self_eq_norm_sq]
    simp only [Pi.inv_apply]
    match_scalars <;> field_simp <;> ring
  have hAconst : ∀ t, A t = A 0 := fun t =>
    is_const_of_deriv_eq_zero (fun s => (hA s).differentiableAt) (fun s => (hA s).deriv) t 0
  intro t
  show ‖x t‖ + inner ℝ (A 0) (x t) = _
  rw [← hAconst t]
  have hr : 0 < ‖x t‖ := norm_pos_iff.mpr (h.ne_origin t)
  show ‖x t‖ + inner ℝ (k⁻¹ • cross (vel x t) hc - ‖x t‖⁻¹ • x t) (x t) = _
  rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    ← hct t, W8_DynamicsRelativity_scalar_triple]
  field_simp
  ring


lemma W8_DynamicsRelativity_lagrange (a b : Vec) : ‖cross a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - (inner ℝ a b) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  unfold cross
  simp [cross_apply, PiLp.inner_apply, Fin.sum_univ_three]; ring

lemma W8_DynamicsRelativity_perp_left (a b : Vec) : inner ℝ a (cross a b) = 0 := by
  unfold cross
  simp [cross_apply, PiLp.inner_apply, Fin.sum_univ_three]; ring

lemma W8_DynamicsRelativity_perp_right (a b : Vec) : inner ℝ b (cross a b) = 0 := by
  unfold cross
  simp [cross_apply, PiLp.inner_apply, Fin.sum_univ_three]; ring

lemma W8_DynamicsRelativity_perp_right' (a b : Vec) : inner ℝ (cross a b) b = 0 := by
  rw [real_inner_comm]; exact W8_DynamicsRelativity_perp_right a b

lemma W8_DynamicsRelativity_normL {m : ℝ} {x : ℝ → Vec} (hm : 0 < m) :
    ‖angularMomentum m x 0‖ / m = ‖cross (x 0) (vel x 0)‖ := by
  unfold angularMomentum
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hm]
  field_simp


theorem W8_DynamicsRelativity_energy_const {k m : ℝ} {x : ℝ → Vec} (h : KeplerMotion k m x)
    (t : ℝ) : keplerEnergy k m x t = keplerEnergy k m x 0 := by
  have hm := h.mass_pos
  have hx1 : Differentiable ℝ x := h.smooth.differentiable (by norm_num)
  have hv1 : Differentiable ℝ (vel x) := by
    have : ContDiff ℝ 1 (deriv x) := h.smooth.iterate_deriv' 1 1
    exact this.differentiable (by norm_num)
  have hd : ∀ s, HasDerivAt (keplerEnergy k m x) 0 s := by
    intro s
    have hr : 0 < ‖x s‖ := norm_pos_iff.mpr (h.ne_origin s)
    have hxd : HasDerivAt x (vel x s) s := (hx1 s).hasDerivAt
    have hvd : HasDerivAt (vel x) (acc x s) s := (hv1 s).hasDerivAt
    have hx2 : HasDerivAt (fun u => ‖x u‖ ^ 2) (2 * inner ℝ (x s) (vel x s)) s := hxd.norm_sq
    have hn : HasDerivAt (fun u => ‖x u‖) (2 * inner ℝ (x s) (vel x s) / (2 * ‖x s‖)) s := by
      have := hx2.sqrt (by positivity)
      simp only [Real.sqrt_sq (norm_nonneg _)] at this
      convert this using 2
    have hv2 : HasDerivAt (fun u => ‖vel x u‖ ^ 2) (2 * inner ℝ (vel x s) (acc x s)) s :=
      hvd.norm_sq
    have hE := ((hv2.const_mul ((1 / 2) * m)).sub ((hn.inv hr.ne').const_mul (k * m)))
    have hfun : keplerEnergy k m x = fun u => (1 / 2) * m * ‖vel x u‖ ^ 2 - k * m * ‖x u‖⁻¹ := by
      funext u; unfold keplerEnergy; ring
    rw [hfun]
    refine hE.congr_deriv ?_
    have ha : acc x s = (-k / ‖x s‖ ^ 3) • x s := by
      have := h.eom s
      simp only [keplerForce] at this
      rw [← inv_smul_smul₀ hm.ne' (acc x s), this, smul_smul]
      congr 1
      field_simp
    rw [ha, real_inner_smul_right, real_inner_comm (x s) (vel x s)]
    field_simp
    ring
  exact is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0

theorem solution {k m r₀ : ℝ} {x : ℝ → Vec} {A : Vec}
    (hk : 0 < k) (h : KeplerMotion k m x) (hL : angularMomentum m x 0 ≠ 0)
    (hr₀ : r₀ = (‖angularMomentum m x 0‖ / m) ^ 2 / k)
    (hA : ∀ t, ‖x t‖ + inner ℝ A (x t) = r₀)
    (hAL : inner ℝ A (angularMomentum m x 0) = 0) (t : ℝ) :
    keplerEnergy k m x t =
      m * k ^ 2 * (‖A‖ ^ 2 - 1) / (2 * (‖angularMomentum m x 0‖ / m) ^ 2) := by
  have hm := h.mass_pos
  have hx1 : Differentiable ℝ x := h.smooth.differentiable (by norm_num)
  set h0 := cross (x 0) (vel x 0) with hh0def
  set AL := k⁻¹ • cross (vel x 0) h0 - ‖x 0‖⁻¹ • x 0 with hALdef
  have hLn := W8_DynamicsRelativity_normL (x := x) hm
  have hh0 : h0 ≠ 0 := by
    intro h0z; apply hL; unfold angularMomentum; rw [← hh0def, h0z, smul_zero]
  have hw : ∀ t, inner ℝ (A - AL) (x t) = 0 := by
    intro t
    have h1 := hA t
    have h2 := W8_DynamicsRelativity_conic_main hk h t
    rw [hr₀, hLn] at h1
    rw [inner_sub_left]
    linarith
  have hwv : inner ℝ (A - AL) (vel x 0) = 0 := by
    have hd := (innerSL ℝ (A - AL)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hx1 0).hasDerivAt
    simp only [Function.comp_def, innerSL_apply_apply] at hd
    have hfun : (fun t => inner ℝ (A - AL) (x t)) = fun _ => (0 : ℝ) := funext hw
    rw [hfun] at hd
    exact hd.unique (hasDerivAt_const 0 0)
  have hwh : inner ℝ (A - AL) h0 = 0 := by
    have hA0 : inner ℝ A h0 = 0 := by
      unfold angularMomentum at hAL
      rw [← hh0def, real_inner_smul_right] at hAL
      rcases mul_eq_zero.mp hAL with h' | h'
      · exact absurd h' hm.ne'
      · exact h'
    have hAL0 : inner ℝ AL h0 = 0 := by
      rw [hALdef, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
        W8_DynamicsRelativity_perp_right', hh0def, W8_DynamicsRelativity_perp_left]
      ring
    rw [inner_sub_left, hA0, hAL0, sub_zero]
  have hw0 : A - AL = 0 := by
    have hc0 : cross (A - AL) h0 = 0 := by
      rw [hh0def, W8_DynamicsRelativity_triple, hwv, hw 0, zero_smul, zero_smul, sub_zero]
    have hlag := W8_DynamicsRelativity_lagrange (A - AL) h0
    rw [hc0, hwh, norm_zero] at hlag
    have hprod : ‖A - AL‖ ^ 2 * ‖h0‖ ^ 2 = 0 := by nlinarith
    have hh0' : ‖h0‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hh0)
    have hn2 : ‖A - AL‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp hprod with h' | h'
      · exact h'
      · exact absurd h' hh0'
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hn2)
  have hAeq : A = AL := sub_eq_zero.mp hw0
  have hr : 0 < ‖x 0‖ := norm_pos_iff.mpr (h.ne_origin 0)
  have hvh : inner ℝ (vel x 0) h0 = 0 := by
    rw [real_inner_comm, hh0def]; exact W8_DynamicsRelativity_perp_right' _ _
  have hcc : inner ℝ (cross (vel x 0) h0) (cross (vel x 0) h0) = ‖vel x 0‖ ^ 2 * ‖h0‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq, W8_DynamicsRelativity_lagrange, hvh]; ring
  have hcx : inner ℝ (cross (vel x 0) h0) (x 0) = ‖h0‖ ^ 2 := by
    rw [hh0def]; exact W8_DynamicsRelativity_scalar_triple _ _
  have hxc : inner ℝ (x 0) (cross (vel x 0) h0) = ‖h0‖ ^ 2 := by
    rw [real_inner_comm]; exact hcx
  have key : ‖AL‖ ^ 2 = 1 + 2 * ‖h0‖ ^ 2 * keplerEnergy k m x 0 / (m * k ^ 2) := by
    rw [← real_inner_self_eq_norm_sq, hALdef]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [hcc, hcx, hxc, real_inner_self_eq_norm_sq]
    unfold keplerEnergy
    field_simp
    ring
  have hpos : 0 < ‖h0‖ ^ 2 := by positivity
  rw [W8_DynamicsRelativity_energy_const h t, hLn, ← hh0def, hAeq, key]
  field_simp
  ring
