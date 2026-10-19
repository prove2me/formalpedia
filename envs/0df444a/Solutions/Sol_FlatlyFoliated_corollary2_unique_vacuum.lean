-- Prove2me | solution 1 for FlatlyFoliated.corollary2_unique_vacuum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T18:27:53.40008+00:00
-- url     : https://prove2.me/submissions/b35454e7-4805-493a-b72b-f4e61328bf76

import Theorems.Thm_FlatlyFoliated_radial_vacuum_identities
import Theorems.Thm_FlatlyFoliated_theorem2_equivalence
import Theorems.Thm_FlatlyFoliated_theorem5_unique_elliptic_vacuum
import Theorems.Thm_FlatlyFoliated_asymptotic_helmholtz_potential

open scoped ContDiff Topology
open FlatlyFoliated Filter Set Metric

namespace VacuumCorollary

set_option backward.isDefEq.respectTransparency false
attribute [local instance] PiLp.normedAddCommGroup PiLp.normedSpace

private noncomputable abbrev axis (r : ℝ) : R3 := EuclideanSpace.single 0 r

private lemma axis_norm {r : ℝ} (hr : 0 ≤ r) : ‖axis r‖ = r := by
  simp [axis, Real.norm_eq_abs, abs_of_nonneg hr]

private lemma axis_smooth : ContDiff ℝ ∞ axis := by
  have he : axis = fun r : ℝ => r • axis 1 := by ext r i; simp [axis]
  rw [he]
  exact contDiff_id.smul contDiff_const

private lemma smooth_comp {w : R3 → R3} (hw : ContDiff ℝ ∞ w) (i : Fin 3) :
    ContDiff ℝ ∞ (comp w i) :=
  (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp hw

private lemma smooth_pd {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin 3) :
    ContDiff ℝ ∞ (pd i u) :=
  (hu.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

private lemma smooth_grad {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (grad f) :=
  ContDiff.sum fun i _ => (smooth_pd hf i).smul contDiff_const

private lemma exterior_lapse (Λ : ℝ) (hΛ : 0 < Λ) (w : R3 → R3) (η : R3 → ℝ)
    (hw : ContDiff ℝ ∞ w) (hη : ContDiff ℝ ∞ η) (hηpos : ∀ x, 0 < η x)
    (heq : FFREquations Λ 0 0 w η) (hsph : SphSymmAtInfty w η) :
    ∃ c : ℝ, 0 < c ∧ ∃ B : ℝ, 0 < B ∧ ∀ x : R3, B < ‖x‖ → η x = c := by
  obtain ⟨R, hR, hrad⟩ := radial_vacuum_identities Λ w η hw hη hηpos heq hsph
  let a : ℝ → ℝ := fun r => w (axis r) 0
  let e : ℝ → ℝ := fun r => η (axis r)
  have ha : Differentiable ℝ a :=
    ((smooth_comp hw 0).comp axis_smooth).differentiable (by simp)
  have he : Differentiable ℝ e := (hη.comp axis_smooth).differentiable (by simp)
  have hane : ∀ r, R < r → a r ≠ 0 := by
    intro r hr hz
    have hd := (hasDerivAt_id r).mul ((ha r).hasDerivAt.pow 2)
    have hh := hd.unique (hrad r hr).1
    have hp : 0 < Λ * r ^ 2 * e r ^ 2 :=
      mul_pos (mul_pos hΛ (sq_pos_of_pos (hR.trans hr))) (sq_pos_of_pos (hηpos _))
    change 1 * a r ^ 2 + r * ((2 : ℝ) * a r ^ (2 - 1) * deriv a r) = _ at hh
    change _ = Λ * r ^ 2 * e r ^ 2 at hh
    have hzprod : (0 : ℝ) = Λ * r ^ 2 * e r ^ 2 := by
      calc
        0 = 1 * a r ^ 2 + r * ((2 : ℝ) * a r ^ (2 - 1) * deriv a r) := by simp [hz]
        _ = _ := hh
    exact (ne_of_gt hp) hzprod.symm
  obtain ⟨c, hc⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero
    (convex_Ioi R).isPreconnected he.differentiableOn (by
      intro r hr
      exact (mul_eq_zero.mp (hrad r hr).2).resolve_left (hane r hr))
  have hcpos : 0 < c := by rw [← hc (R + 1) (by simp)]; exact hηpos _
  obtain ⟨R₀, hR₀, hs⟩ := hsph
  refine ⟨c, hcpos, max R R₀, lt_max_of_lt_left hR, ?_⟩
  intro x hx
  have hr : R < ‖x‖ := lt_of_le_of_lt (le_max_left _ _) hx
  let y := axis ‖x‖
  have hy : ‖y‖ = ‖x‖ := axis_norm (norm_nonneg x)
  let T := (Submodule.span ℝ {y - x})ᗮ.reflection
  have ht : T y = x := Submodule.reflection_sub hy
  have hh := (hs T y (by rw [hy]; exact le_trans (le_max_right _ _) hx.le)).1
  rw [ht] at hh
  exact hh.trans (hc ‖x‖ hr)

private lemma pd_scale {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (a : ℝ) (i : Fin 3) :
    pd i (fun x => a * u x) = fun x => a * pd i u x := by
  ext x
  rw [pd, ((hasFDerivAt_const a x).fun_mul (hu.differentiable (by simp) x).hasFDerivAt).fderiv]
  simp [pd]

private lemma comp_scale (w : R3 → R3) (a : ℝ) (i : Fin 3) :
    comp (fun x => a • w x) i = fun x => a * comp w i x := rfl

private lemma div_scale {w : R3 → R3} (hw : ContDiff ℝ ∞ w) (a : ℝ) :
    divg (fun x => a • w x) = fun x => a * divg w x := by
  ext x
  simp only [divg, comp_scale, pd_scale (smooth_comp hw _), Finset.mul_sum]

private lemma lap_scale {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (a : ℝ) :
    lap (fun x => a * u x) = fun x => a * lap u x := by
  ext x
  simp only [lap, pd_scale hu, pd_scale (smooth_pd hu _), Finset.mul_sum]

private lemma scale_vacuum (Λ : ℝ) (w : R3 → R3) (η : R3 → ℝ)
    (hw : ContDiff ℝ ∞ w) (hη : ContDiff ℝ ∞ η) (hηpos : ∀ x, 0 < η x)
    (heq : FFREquations Λ 0 0 w η) (a : ℝ) (ha : a ≠ 0) :
    FFREquations Λ 0 0 (fun x => a • w x) (fun x => a * η x) := by
  intro x
  have hx : η x ≠ 0 := (hηpos x).ne'
  constructor
  · have h := (heq x).1
    dsimp only [Eq34] at h ⊢
    simp only [Pi.zero_apply, mul_zero, add_zero] at h ⊢
    rw [div_scale hw]
    simp only [comp_scale, pd_scale (smooth_comp hw _)]
    rw [h]
    have hs : (∑ i, ∑ j, (a * pd j (comp w i) x + a * pd i (comp w j) x) ^ 2) =
        a ^ 2 * ∑ i, ∑ j, (pd j (comp w i) x + pd i (comp w j) x) ^ 2 := by
      simp only [Finset.mul_sum]
      congr 1; ext i; congr 1; ext j; ring
    rw [hs]
    field_simp [ha, hx]
  · intro i
    have h := (heq x).2 i
    dsimp only [Eq35] at h ⊢
    simp only [Pi.zero_apply] at h ⊢
    rw [comp_scale, lap_scale (smooth_comp hw i), div_scale hw]
    simp only [comp_scale, pd_scale (smooth_comp hw _), pd_scale hη]
    have hd : ContDiff ℝ ∞ (divg w) := ContDiff.sum fun j _ => smooth_pd (smooth_comp hw j) j
    rw [pd_scale hd]
    rw [h]
    have hs : (∑ j, (a * pd j (comp w i) x + a * pd i (comp w j) x) * (a * pd j η x)) =
        a ^ 2 * ∑ j, (pd j (comp w i) x + pd i (comp w j) x) * pd j η x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hs]
    field_simp [ha, hx]

private lemma pd_quad_const (a b : ℝ) (i : Fin 3) :
    pd i (fun x : R3 => a * ‖x‖ ^ 2 + b) = fun x => 2 * a * x i := by
  ext x
  have h := ((hasFDerivAt_const a x).fun_mul
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt).add_const b
  rw [pd, h.fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

private lemma grad_quad_const (a b : ℝ) :
    grad (fun x : R3 => a * ‖x‖ ^ 2 + b) = fun x => (2 * a) • x := by
  ext x i
  simp [grad, pd_quad_const, Pi.single_apply]

private lemma sqrt_scale (Λ : ℝ) : Real.sqrt (Λ / 3) = 2 * Real.sqrt (Λ / 12) := by
  rw [show Λ / 3 = 4 * (Λ / 12) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

private lemma existence (Λ : ℝ) (hΛ : 0 < Λ) :
    ContDiff ℝ ∞ (fun x : R3 => Real.sqrt (Λ / 3) • x) ∧
      (∀ x, 0 < divg (fun x : R3 => Real.sqrt (Λ / 3) • x) x / 1) ∧
      FFREquations Λ 0 0 (fun x : R3 => Real.sqrt (Λ / 3) • x) (fun _ => 1) ∧
      SphSymmAtInfty (fun x : R3 => Real.sqrt (Λ / 3) • x) (fun _ => 1) := by
  obtain ⟨hf, hpos, hsys, _⟩ := (theorem5_unique_elliptic_vacuum Λ hΛ).1
  let q : R3 → ℝ := fun x => Real.sqrt (Λ / 12) * ‖x‖ ^ 2
  have hgrad : grad q = fun x => Real.sqrt (Λ / 3) • x := by
    have hq : q = fun x : R3 => Real.sqrt (Λ / 12) * ‖x‖ ^ 2 + 0 := by ext x; simp [q]
    rw [hq, grad_quad_const, sqrt_scale]
  have hs := (theorem2_equivalence Λ 0 0 (fun _ => 1) contDiff_const contDiff_const
    contDiff_const (by intro x; norm_num)).2 q 0 hf contDiff_const hsys
  have hw0 : (fun x => grad q x + (0 : R3 → R3) x) = fun x => Real.sqrt (Λ / 3) • x := by
    simp only [hgrad, Pi.zero_apply, add_zero]
  rw [hw0] at hs
  refine ⟨(contDiff_const (c := Real.sqrt (Λ / 3))).smul (contDiff_id (E := R3)), ?_, hs.1, ?_⟩
  · intro x
    rw [div_one, ← hs.2 x]
    exact hpos x
  · refine ⟨1, by norm_num, ?_⟩
    intro T x _
    simp only [map_smul, and_self]

private lemma uniqueness (Λ : ℝ) (hΛ : 0 < Λ) (w : R3 → R3) (η : R3 → ℝ)
    (hw : ContDiff ℝ ∞ w) (hη : ContDiff ℝ ∞ η) (hηpos : ∀ x, 0 < η x)
    (hconv : ∀ x, 0 < divg w x / η x) (heq : FFREquations Λ 0 0 w η)
    (hsph : SphSymmAtInfty w η) :
    ∃ c : ℝ, 0 < c ∧ η = (fun _ => c) ∧
      w = fun x => (c * Real.sqrt (Λ / 3)) • x := by
  obtain ⟨c, hc, B, _, hext⟩ := exterior_lapse Λ hΛ w η hw hη hηpos heq hsph
  let W : R3 → R3 := fun x => c⁻¹ • w x
  let E : R3 → ℝ := fun x => c⁻¹ * η x
  have hW : ContDiff ℝ ∞ W := (contDiff_const (c := (c⁻¹ : ℝ))).smul hw
  have hE : ContDiff ℝ ∞ E := contDiff_const.mul hη
  have hEpos : ∀ x, 0 < E x := fun x => mul_pos (inv_pos.mpr hc) (hηpos x)
  have heq' : FFREquations Λ 0 0 W E :=
    scale_vacuum Λ w η hw hη hηpos heq c⁻¹ (inv_ne_zero hc.ne')
  have hEinfty : Tendsto E (Bornology.cobounded R3) (𝓝 1) := by
    have hevent : (fun _ : R3 => (1 : ℝ)) =ᶠ[Bornology.cobounded R3] E := by
      filter_upwards [eventually_cobounded_le_norm (B + 1)] with x hx
      dsimp [E]
      rw [hext x (by linarith), inv_mul_cancel₀ hc.ne']
    exact tendsto_const_nhds.congr' hevent
  obtain ⟨R, hR, hs⟩ := hsph
  obtain ⟨f, hf, hlap, happ, hzinf⟩ := asymptotic_helmholtz_potential W hW
    ⟨R, hR, by intro T x hx; dsimp [W]; rw [(hs T x hx).2, map_smul]⟩
  let z : R3 → R3 := fun x => W x - grad f x
  have hz : ContDiff ℝ ∞ z := hW.sub (smooth_grad hf)
  have hsys : EllipticSystem Λ 0 0 f z E :=
    (theorem2_equivalence Λ 0 0 E contDiff_const contDiff_const hE hEpos).1 W f hW hf heq' hlap
  have hconv' : ∀ x, 0 < lap f x / E x := by
    intro x
    rw [hlap x]
    have hd : divg W x = c⁻¹ * divg w x := congrFun (div_scale hw c⁻¹) x
    rw [hd]
    change 0 < c⁻¹ * divg w x / (c⁻¹ * η x)
    have he : c⁻¹ * divg w x / (c⁻¹ * η x) = divg w x / η x := by
      field_simp
    rw [he]
    exact hconv x
  obtain ⟨d, hfd, hz0, hE1⟩ := (theorem5_unique_elliptic_vacuum Λ hΛ).2
    f z E hf hz hE hEpos hconv' hsys happ hzinf hEinfty
  have hgf : grad f = fun x => Real.sqrt (Λ / 3) • x := by
    rw [show f = (fun x : R3 => Real.sqrt (Λ / 12) * ‖x‖ ^ 2 + d) from funext hfd,
      grad_quad_const, sqrt_scale]
  refine ⟨c, hc, ?_, ?_⟩
  · ext x
    have h := congrFun hE1 x
    change c⁻¹ * η x = 1 at h
    calc
      η x = c * (c⁻¹ * η x) := by rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
      _ = c := by rw [h, mul_one]
  · ext x i
    have h := congrFun hz0 x
    change W x - grad f x = 0 at h
    have hWx : W x = Real.sqrt (Λ / 3) • x := by simpa only [hgf] using sub_eq_zero.mp h
    have he : w x = c • W x := by dsimp [W]; rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    rw [he, hWx, smul_smul]

end VacuumCorollary

open VacuumCorollary

theorem solution (Λ : ℝ) (hΛ : 0 < Λ) :
    (ContDiff ℝ ∞ (fun x : R3 => Real.sqrt (Λ / 3) • x) ∧
      (∀ x, 0 < divg (fun x : R3 => Real.sqrt (Λ / 3) • x) x / 1) ∧
      FFREquations Λ 0 0 (fun x : R3 => Real.sqrt (Λ / 3) • x) (fun _ => 1) ∧
      SphSymmAtInfty (fun x : R3 => Real.sqrt (Λ / 3) • x) (fun _ => 1)) ∧
    ∀ (w : R3 → R3) (η : R3 → ℝ),
      ContDiff ℝ ∞ w → ContDiff ℝ ∞ η → (∀ x, 0 < η x) → (∀ x, 0 < divg w x / η x) →
      FFREquations Λ 0 0 w η → SphSymmAtInfty w η →
      ∃ c : ℝ, 0 < c ∧ η = (fun _ => c) ∧ w = fun x => (c * Real.sqrt (Λ / 3)) • x := by
  exact ⟨existence Λ hΛ, uniqueness Λ hΛ⟩
