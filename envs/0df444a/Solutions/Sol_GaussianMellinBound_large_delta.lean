-- Prove2me | solution 1 for GaussianMellinBound.large_delta
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T00:13:39.584474+00:00
-- url     : https://prove2.me/submissions/8e06299f-f352-4b2c-8026-f225cd884fcd

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ParametricIntegral

open Real Complex MeasureTheory Filter Set
open scoped Topology

noncomputable section

private lemma integrableOn_rpow_mul_exp_neg_mul_Ioi {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    IntegrableOn (fun r : ℝ => r ^ (a - 1) * Real.exp (-(c * r))) (Ioi 0) := by
  have h0 := Real.GammaIntegral_convergent ha
  have h1 : IntegrableOn (fun r : ℝ => Real.exp (-(c * r)) * (c * r) ^ (a - 1)) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff (fun u : ℝ => Real.exp (-u) * u ^ (a - 1)) 0 hc).mpr
      (by simpa [mul_zero] using h0)
    simpa [Function.comp] using this
  have h2 : IntegrableOn (fun r : ℝ => c ^ (1 - a) * (Real.exp (-(c * r)) * (c * r) ^ (a - 1))) (Ioi 0) :=
    h1.const_mul _
  refine IntegrableOn.congr_fun h2 (fun r hr => ?_) measurableSet_Ioi
  have hr0 : 0 < r := hr
  rw [Real.mul_rpow hc.le hr0.le]
  have hc_pow : c ^ (1 - a) * c ^ (a - 1) = 1 := by
    rw [← Real.rpow_add hc]
    norm_num
  calc
    c ^ (1 - a) * (Real.exp (-(c * r)) * (c ^ (a - 1) * r ^ (a - 1)))
        = (c ^ (1 - a) * c ^ (a - 1)) * (r ^ (a - 1) * Real.exp (-(c * r))) := by ring
    _ = r ^ (a - 1) * Real.exp (-(c * r)) := by rw [hc_pow, one_mul]

private lemma exp_neg_mul_sq_le (α r : ℝ) (_hα : 0 ≤ α) :
    Real.exp (-(α * r ^ 2)) ≤ Real.exp (α / 4) * Real.exp (-(α * r)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsq : 0 ≤ (r - 1 / 2) ^ 2 := sq_nonneg (r - 1 / 2)
  nlinarith

private def rayWeight (σ τ : ℝ) : ℂ :=
  1 + ((τ * σ : ℝ) : ℂ) * Complex.I

private lemma rayWeight_mem_slitPlane (σ τ : ℝ) : rayWeight σ τ ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  simp [rayWeight]

private lemma rayWeight_ne_zero (σ τ : ℝ) : rayWeight σ τ ≠ 0 :=
  Complex.slitPlane_ne_zero (rayWeight_mem_slitPlane σ τ)

private lemma norm_rayWeight_sq (σ τ : ℝ) (hσ : σ ^ 2 = 1) :
    ‖rayWeight σ τ‖ ^ 2 = 1 + τ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [rayWeight]
  linear_combination τ ^ 2 * hσ

private lemma norm_rayWeight_le_two (σ τ : ℝ) (hσ : σ ^ 2 = 1) (hτ0 : -1 ≤ τ) (hτ1 : τ ≤ 1) :
    ‖rayWeight σ τ‖ ≤ 2 := by
  have hnorm_sq := norm_rayWeight_sq σ τ hσ
  nlinarith [norm_nonneg (rayWeight σ τ), hnorm_sq, sq_nonneg τ, hτ0, hτ1]

private lemma norm_rayWeight_ge_one (σ τ : ℝ) :
    1 ≤ ‖rayWeight σ τ‖ := by
  have hre : (rayWeight σ τ).re = 1 := by simp [rayWeight]
  linarith [Complex.re_le_norm (rayWeight σ τ)]

private lemma norm_rayWeight_cpow_le {s : ℂ} (hre : s.re = 1 / 2) (σ τ : ℝ)
    (hσ : σ ^ 2 = 1) (hτ0 : -1 ≤ τ) (hτ1 : τ ≤ 1) :
    ‖rayWeight σ τ ^ s‖ ≤ 2 * Real.exp (|s.im| * Real.pi) := by
  rw [Complex.norm_cpow_of_ne_zero (rayWeight_ne_zero σ τ) s, hre]
  have hnorm_le := norm_rayWeight_le_two σ τ hσ hτ0 hτ1
  have hrpow_le : ‖rayWeight σ τ‖ ^ (1 / 2 : ℝ) ≤ 2 := by
    have h1 : ‖rayWeight σ τ‖ ^ (1 / 2 : ℝ) ≤ (4 : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg _) (by linarith) (by norm_num)
    have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  have harg : -((rayWeight σ τ).arg * s.im) ≤ |s.im| * Real.pi := by
    have harg_abs : |(rayWeight σ τ).arg| ≤ Real.pi := Complex.abs_arg_le_pi _
    have hmul : |(rayWeight σ τ).arg * s.im| ≤ |s.im| * Real.pi := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left harg_abs (abs_nonneg _)
    exact le_trans (neg_le_abs _) hmul
  rw [div_eq_mul_inv, ← Real.exp_neg]
  exact mul_le_mul hrpow_le (Real.exp_le_exp.mpr harg) (Real.exp_nonneg _) (by norm_num)

private def rayExp (z₀ : ℂ) (α σ τ r : ℝ) : ℂ :=
  -((α : ℂ) * rayWeight σ τ ^ 2 * (r : ℂ) ^ 2) - z₀ * rayWeight σ τ * (r : ℂ)

private def rayIntegrand (s z₀ : ℂ) (α σ τ r : ℝ) : ℂ :=
  rayWeight σ τ ^ s * (r : ℂ) ^ (s - 1) * Complex.exp (rayExp z₀ α σ τ r)

private def rayPrim (s z₀ : ℂ) (α σ τ r : ℝ) : ℂ :=
  rayWeight σ τ ^ s * (r : ℂ) ^ s * Complex.exp (rayExp z₀ α σ τ r)

private lemma rayExp_re (z₀ : ℂ) (α σ τ r : ℝ) (hσ : σ ^ 2 = 1) :
    (rayExp z₀ α σ τ r).re = -(α * (1 - τ ^ 2) * r ^ 2) - (z₀.re - τ * σ * z₀.im) * r := by
  simp only [rayExp, rayWeight, sq]
  simp
  linear_combination α * r ^ 2 * τ ^ 2 * hσ

private lemma norm_rayIntegrand_eq {s z₀ : ℂ} (hre : s.re = 1 / 2) (α σ τ : ℝ) (hσ : σ ^ 2 = 1)
    {r : ℝ} (hr : 0 < r) :
    ‖rayIntegrand s z₀ α σ τ r‖ =
      ‖rayWeight σ τ ^ s‖ * r ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(α * (1 - τ ^ 2) * r ^ 2) - (z₀.re - τ * σ * z₀.im) * r) := by
  simp only [rayIntegrand, norm_mul, Complex.norm_exp, rayExp_re z₀ α σ τ r hσ]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  have hs1 : (s - 1).re = -(1 / 2 : ℝ) := by simp [hre]; norm_num
  rw [hs1]

private lemma norm_rayPrim_eq {s z₀ : ℂ} (hre : s.re = 1 / 2) (α σ τ : ℝ) (hσ : σ ^ 2 = 1)
    {r : ℝ} (hr : 0 < r) :
    ‖rayPrim s z₀ α σ τ r‖ =
      ‖rayWeight σ τ ^ s‖ * r ^ (1 / 2 : ℝ) *
        Real.exp (-(α * (1 - τ ^ 2) * r ^ 2) - (z₀.re - τ * σ * z₀.im) * r) := by
  simp only [rayPrim, norm_mul, Complex.norm_exp, rayExp_re z₀ α σ τ r hσ]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr, hre]

private lemma hasDerivAt_rayWeight (σ τ : ℝ) :
    HasDerivAt (fun u : ℝ => rayWeight σ u) ((σ : ℂ) * Complex.I) τ := by
  unfold rayWeight
  have h1 : HasDerivAt (fun u : ℝ => ((u * σ : ℝ) : ℂ)) (σ : ℂ) τ := by
    have := (hasDerivAt_id τ).mul_const σ
    simpa using this.ofReal_comp
  simpa using (h1.mul_const Complex.I).const_add (1 : ℂ)

private lemma hasDerivAt_rayIntegrand_tau (s z₀ : ℂ) (α σ τ : ℝ) {r : ℝ} (_hr : 0 < r) :
    HasDerivAt (fun u : ℝ => rayIntegrand s z₀ α σ u r)
      (((σ : ℂ) * Complex.I / rayWeight σ τ) *
        ((s - 2 * (α : ℂ) * rayWeight σ τ ^ 2 * (r : ℂ) ^ 2 - z₀ * rayWeight σ τ * (r : ℂ)) *
          rayIntegrand s z₀ α σ τ r)) τ := by
  have hw := hasDerivAt_rayWeight σ τ
  have hws : HasDerivAt (fun u : ℝ => rayWeight σ u ^ s)
      (s * rayWeight σ τ ^ (s - 1) * ((σ : ℂ) * Complex.I)) τ :=
    (Complex.hasStrictDerivAt_cpow_const (rayWeight_mem_slitPlane σ τ)).hasDerivAt.comp τ hw
  have hw2 : HasDerivAt (fun u : ℝ => rayWeight σ u ^ 2)
      (2 * rayWeight σ τ * ((σ : ℂ) * Complex.I)) τ := by
    simpa [sq] using (hw.fun_mul hw).congr_deriv (by ring)
  have hexp_arg : HasDerivAt (fun u : ℝ => rayExp z₀ α σ u r)
      (-((α : ℂ) * (2 * rayWeight σ τ * ((σ : ℂ) * Complex.I)) * (r : ℂ) ^ 2) -
        z₀ * ((σ : ℂ) * Complex.I) * (r : ℂ)) τ := by
    unfold rayExp
    exact ((hw2.const_mul (α : ℂ)).mul_const ((r : ℂ) ^ 2)).neg.sub
      ((hw.const_mul z₀).mul_const (r : ℂ))
  have hexp := hexp_arg.cexp
  have hprod := (hws.mul_const ((r : ℂ) ^ (s - 1))).mul hexp
  refine hprod.congr_deriv ?_
  have hw_ne := rayWeight_ne_zero σ τ
  have hws_split : rayWeight σ τ ^ s = rayWeight σ τ ^ (s - 1) * rayWeight σ τ := by
    symm
    calc
      rayWeight σ τ ^ (s - 1) * rayWeight σ τ
          = rayWeight σ τ ^ (s - 1) * rayWeight σ τ ^ (1 : ℂ) := by rw [Complex.cpow_one]
      _ = rayWeight σ τ ^ s := by
          rw [← Complex.cpow_add _ _ hw_ne]
          congr 1; ring
  unfold rayIntegrand
  rw [div_eq_mul_inv]
  calc
    s * rayWeight σ τ ^ (s - 1) * (↑σ * I) * ↑r ^ (s - 1) * cexp (rayExp z₀ α σ τ r) +
        rayWeight σ τ ^ s * ↑r ^ (s - 1) *
          (cexp (rayExp z₀ α σ τ r) *
            (-(↑α * (2 * rayWeight σ τ * (↑σ * I)) * ↑r ^ 2) - z₀ * (↑σ * I) * ↑r))
      = (↑σ * I * (rayWeight σ τ)⁻¹) *
          ((s * (rayWeight σ τ ^ (s - 1) * rayWeight σ τ) -
            (2 * ↑α * rayWeight σ τ ^ 2 * ↑r ^ 2 + z₀ * rayWeight σ τ * ↑r) * rayWeight σ τ ^ s) *
            ↑r ^ (s - 1) * cexp (rayExp z₀ α σ τ r)) := by
        field_simp [hw_ne]
        ring
    _ = ↑σ * I * (rayWeight σ τ)⁻¹ *
          ((s - 2 * ↑α * rayWeight σ τ ^ 2 * ↑r ^ 2 - z₀ * rayWeight σ τ * ↑r) *
            (rayWeight σ τ ^ s * ↑r ^ (s - 1) * cexp (rayExp z₀ α σ τ r))) := by
        rw [← hws_split]
        ring

private lemma hasDerivAt_rayPrim_r (s z₀ : ℂ) (hs : s ≠ 0) (α σ τ : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun u : ℝ => rayPrim s z₀ α σ τ u)
      ((s - 2 * (α : ℂ) * rayWeight σ τ ^ 2 * (r : ℂ) ^ 2 - z₀ * rayWeight σ τ * (r : ℂ)) *
        rayIntegrand s z₀ α σ τ r) r := by
  have hrs : HasDerivAt (fun u : ℝ => (u : ℂ) ^ s) (s * (r : ℂ) ^ (s - 1)) r :=
    hasDerivAt_ofReal_cpow_const hr.ne' hs
  have hr1 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 r := by
    simpa using (hasDerivAt_id r).ofReal_comp
  have hr2 : HasDerivAt (fun u : ℝ => (u : ℂ) ^ 2) (2 * (r : ℂ)) r := by
    simpa [sq] using (hr1.fun_mul hr1).congr_deriv (by ring)
  have hexp_arg : HasDerivAt (fun u : ℝ => rayExp z₀ α σ τ u)
      (-((α : ℂ) * rayWeight σ τ ^ 2 * (2 * (r : ℂ))) - z₀ * rayWeight σ τ * 1) r := by
    unfold rayExp
    exact (hr2.const_mul ((α : ℂ) * rayWeight σ τ ^ 2)).neg.sub
      (hr1.const_mul (z₀ * rayWeight σ τ))
  have hexp := hexp_arg.cexp
  have hprod := (hrs.const_mul (rayWeight σ τ ^ s)).mul hexp
  refine hprod.congr_deriv ?_
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hrs_split : (r : ℂ) ^ s = (r : ℂ) ^ (s - 1) * (r : ℂ) := by
    symm
    calc
      (r : ℂ) ^ (s - 1) * (r : ℂ) = (r : ℂ) ^ (s - 1) * (r : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
      _ = (r : ℂ) ^ s := by
          rw [← Complex.cpow_add _ _ hr_ne]
          congr 1; ring
  unfold rayIntegrand
  rw [hrs_split]
  ring

private lemma ray_rotation_eq {s z₀ : ℂ} (hre : s.re = 1 / 2) {α σ : ℝ}
    (hα : 0 ≤ α) (hσ : σ ^ 2 = 1) (hz_re : 0 ≤ z₀.re)
    (hW : 0 < -σ * z₀.im) (h0_decay : 0 < α ∨ 0 < z₀.re) :
    ∫ r : ℝ in Ioi 0, rayIntegrand s z₀ α σ 0 r =
      ∫ r : ℝ in Ioi 0, rayIntegrand s z₀ α σ 1 r := by
  let W := -σ * z₀.im
  let H : ℝ → ℂ := fun τ => ∫ r : ℝ in Ioi 0, rayIntegrand s z₀ α σ τ r
  let Cw : ℝ := 2 * Real.exp (|s.im| * Real.pi)
  have hCw_pos : 0 < Cw := by dsimp [Cw]; positivity
  have hs_ne : s ≠ 0 := by
    intro h; rw [h, zero_re] at hre; norm_num at hre
  have hlin : ∀ τ : ℝ, z₀.re - τ * σ * z₀.im = z₀.re + τ * W := by
    intro τ; dsimp [W]; ring
  have hmeas : ∀ τ : ℝ, AEStronglyMeasurable (fun r : ℝ => rayIntegrand s z₀ α σ τ r)
      (volume.restrict (Ioi 0)) := by
    intro τ
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const ?_) ?_
    · intro r hr
      exact (continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hr))).continuousWithinAt
    · refine Continuous.continuousOn ?_
      unfold rayExp
      fun_prop
  have hderiv_zero : ∀ τ₀ ∈ Ioo (0 : ℝ) 1, HasDerivAt H 0 τ₀ := by
    intro τ₀ hτ₀
    let ε := τ₀ / 2
    have hε : 0 < ε := by dsimp [ε]; linarith [hτ₀.1]
    have hnhds : Ioo ε 1 ∈ 𝓝 τ₀ := Ioo_mem_nhds (by dsimp [ε]; linarith [hτ₀.1]) hτ₀.2
    let c := ε * W
    have hc : 0 < c := mul_pos hε hW
    let F' : ℝ → ℝ → ℂ := fun τ r =>
      ((σ : ℂ) * Complex.I / rayWeight σ τ) *
        ((s - 2 * (α : ℂ) * rayWeight σ τ ^ 2 * (r : ℂ) ^ 2 - z₀ * rayWeight σ τ * (r : ℂ)) *
          rayIntegrand s z₀ α σ τ r)
    let bound : ℝ → ℝ := fun r =>
      2 * Cw * (‖s‖ * r ^ (1 / 2 - 1 : ℝ) + 8 * α * r ^ (5 / 2 - 1 : ℝ) + 2 * ‖z₀‖ * r ^ (3 / 2 - 1 : ℝ)) *
        Real.exp (-(c * r))
    have hbound_int : IntegrableOn bound (Ioi 0) := by
      have i1 : IntegrableOn (fun x => 2 * Cw * ‖s‖ * (x ^ (1 / 2 - 1 : ℝ) * Real.exp (-(c * x)))) (Ioi 0) :=
        (integrableOn_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 1 / 2) hc).const_mul _
      have i2 : IntegrableOn (fun x => 2 * Cw * (8 * α) * (x ^ (5 / 2 - 1 : ℝ) * Real.exp (-(c * x)))) (Ioi 0) :=
        (integrableOn_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 5 / 2) hc).const_mul _
      have i3 : IntegrableOn (fun x => 2 * Cw * (2 * ‖z₀‖) * (x ^ (3 / 2 - 1 : ℝ) * Real.exp (-(c * x)))) (Ioi 0) :=
        (integrableOn_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 3 / 2) hc).const_mul _
      refine IntegrableOn.congr_fun ((i1.add i2).add i3) (fun r _ => ?_) measurableSet_Ioi
      dsimp [bound]; ring
    have hF_int : IntegrableOn (fun r : ℝ => rayIntegrand s z₀ α σ τ₀ r) (Ioi 0) := by
      refine (integrableOn_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 1 / 2) hc |>.const_mul Cw).mono'
        (hmeas τ₀) ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with r hr
      have hr0 : 0 < r := hr
      rw [norm_rayIntegrand_eq hre α σ τ₀ hσ hr0, hlin τ₀]
      have hw_le : ‖rayWeight σ τ₀ ^ s‖ ≤ Cw :=
        norm_rayWeight_cpow_le hre σ τ₀ hσ (by linarith [hτ₀.1]) hτ₀.2.le
      have hexp_le : Real.exp (-(α * (1 - τ₀ ^ 2) * r ^ 2) - (z₀.re + τ₀ * W) * r) ≤ Real.exp (-(c * r)) := by
        apply Real.exp_le_exp.mpr
        have h1mt : 0 ≤ 1 - τ₀ ^ 2 := by nlinarith [hτ₀.1, hτ₀.2]
        have h1 : 0 ≤ α * (1 - τ₀ ^ 2) * r ^ 2 := by positivity
        have h2 : c ≤ z₀.re + τ₀ * W := by dsimp [c, ε]; nlinarith [hτ₀.1, hW, hz_re]
        have h3 : c * r ≤ (z₀.re + τ₀ * W) * r := mul_le_mul_of_nonneg_right h2 hr0.le
        linarith
      have hr_eq : r ^ (-(1 / 2 : ℝ)) = r ^ (1 / 2 - 1 : ℝ) := by norm_num
      rw [hr_eq]
      have hrp_nn : 0 ≤ r ^ (1 / 2 - 1 : ℝ) := Real.rpow_nonneg hr0.le _
      have h_step1 : ‖rayWeight σ τ₀ ^ s‖ * r ^ (1 / 2 - 1 : ℝ) ≤ Cw * r ^ (1 / 2 - 1 : ℝ) :=
        mul_le_mul_of_nonneg_right hw_le hrp_nn
      calc
        ‖rayWeight σ τ₀ ^ s‖ * r ^ (1 / 2 - 1 : ℝ) *
            Real.exp (-(α * (1 - τ₀ ^ 2) * r ^ 2) - (z₀.re + τ₀ * W) * r)
          ≤ (Cw * r ^ (1 / 2 - 1 : ℝ)) * Real.exp (-(c * r)) :=
            mul_le_mul h_step1 hexp_le (Real.exp_nonneg _) (mul_nonneg hCw_pos.le hrp_nn)
        _ = Cw * (r ^ (1 / 2 - 1 : ℝ) * Real.exp (-(c * r))) := by ring
    have hF'_meas : AEStronglyMeasurable (F' τ₀) (volume.restrict (Ioi 0)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      dsimp [F']
      refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul ?_ ?_)
      · refine Continuous.continuousOn ?_; fun_prop
      · refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const ?_) ?_
        · intro r hr
          exact (continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hr))).continuousWithinAt
        · refine Continuous.continuousOn ?_; unfold rayExp; fun_prop
    have hdom : ∀ᵐ r ∂volume.restrict (Ioi 0), ∀ τ ∈ Ioo ε 1, ‖F' τ r‖ ≤ bound r := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with r hr τ hτ
      have hr0 : 0 < r := hr
      have hτ0 : 0 < τ := lt_trans hε hτ.1
      dsimp only [F']
      rw [norm_mul, norm_mul, norm_div]
      have h_pref : ‖(σ : ℂ) * Complex.I‖ / ‖rayWeight σ τ‖ ≤ 2 := by
        have hσ_norm : ‖(σ : ℂ) * Complex.I‖ = 1 := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
          exact sq_eq_one_iff.mp hσ |>.elim (fun h => by simp [h]) (fun h => by simp [h])
        have hw_ge := norm_rayWeight_ge_one σ τ
        rw [hσ_norm]
        exact le_trans (div_le_one_of_le₀ hw_ge (by positivity)) (by norm_num)
      have hw_le2 : ‖rayWeight σ τ‖ ≤ 2 := norm_rayWeight_le_two σ τ hσ (by linarith) hτ.2.le
      have h_poly : ‖s - 2 * (α : ℂ) * rayWeight σ τ ^ 2 * (r : ℂ) ^ 2 - z₀ * rayWeight σ τ * (r : ℂ)‖ ≤
          ‖s‖ + 8 * α * r ^ 2 + 2 * ‖z₀‖ * r := by
        have hw_sq4 : ‖rayWeight σ τ‖ ^ 2 ≤ 4 := by nlinarith [hw_le2, norm_nonneg (rayWeight σ τ)]
        have hp1 : 2 * α * ‖rayWeight σ τ‖ ^ 2 * r ^ 2 ≤ 8 * α * r ^ 2 := by
          have : 2 * α * ‖rayWeight σ τ‖ ^ 2 ≤ 8 * α := by nlinarith [hα, hw_sq4]
          exact mul_le_mul_of_nonneg_right this (sq_nonneg r)
        have hp2 : ‖z₀‖ * ‖rayWeight σ τ‖ * r ≤ 2 * ‖z₀‖ * r := by
          have : ‖z₀‖ * ‖rayWeight σ τ‖ ≤ 2 * ‖z₀‖ := by nlinarith [hw_le2, norm_nonneg z₀]
          exact mul_le_mul_of_nonneg_right this hr0.le
        calc
          ‖s - 2 * (α : ℂ) * rayWeight σ τ ^ 2 * (r : ℂ) ^ 2 - z₀ * rayWeight σ τ * (r : ℂ)‖
            ≤ ‖s - 2 * (α : ℂ) * rayWeight σ τ ^ 2 * (r : ℂ) ^ 2‖ + ‖z₀ * rayWeight σ τ * (r : ℂ)‖ := norm_sub_le _ _
          _ ≤ ‖s‖ + ‖2 * (α : ℂ) * rayWeight σ τ ^ 2 * (r : ℂ) ^ 2‖ + ‖z₀ * rayWeight σ τ * (r : ℂ)‖ := by
              gcongr; exact norm_sub_le _ _
          _ = ‖s‖ + 2 * α * ‖rayWeight σ τ‖ ^ 2 * r ^ 2 + ‖z₀‖ * ‖rayWeight σ τ‖ * r := by
              simp only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg hα, abs_of_pos hr0]
          _ ≤ ‖s‖ + 8 * α * r ^ 2 + 2 * ‖z₀‖ * r := by linarith
      rw [norm_rayIntegrand_eq hre α σ τ hσ hr0, hlin τ]
      have hws_le : ‖rayWeight σ τ ^ s‖ ≤ Cw := norm_rayWeight_cpow_le hre σ τ hσ (by linarith) hτ.2.le
      have hexp_le : Real.exp (-(α * (1 - τ ^ 2) * r ^ 2) - (z₀.re + τ * W) * r) ≤ Real.exp (-(c * r)) := by
        apply Real.exp_le_exp.mpr
        have h1mt : 0 ≤ 1 - τ ^ 2 := by nlinarith [hτ0, hτ.2]
        have h1 : 0 ≤ α * (1 - τ ^ 2) * r ^ 2 := by positivity
        have h2 : c ≤ z₀.re + τ * W := by dsimp [c]; nlinarith [hτ.1, hW, hz_re]
        have h3 : c * r ≤ (z₀.re + τ * W) * r := mul_le_mul_of_nonneg_right h2 hr0.le
        linarith
      have hr2 : r ^ 2 * r ^ (-(1 / 2 : ℝ)) = r ^ (5 / 2 - 1 : ℝ) := by
        rw [← Real.rpow_natCast r 2, ← Real.rpow_add hr0]; norm_num
      have hr1 : r * r ^ (-(1 / 2 : ℝ)) = r ^ (3 / 2 - 1 : ℝ) := by
        calc
          r * r ^ (-(1 / 2 : ℝ)) = r ^ (1 : ℝ) * r ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
          _ = r ^ (3 / 2 - 1 : ℝ) := by rw [← Real.rpow_add hr0]; norm_num
      have hr0' : r ^ (-(1 / 2 : ℝ)) = r ^ (1 / 2 - 1 : ℝ) := by norm_num
      have h_in1 : ‖rayWeight σ τ ^ s‖ * r ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(α * (1 - τ ^ 2) * r ^ 2) - (z₀.re + τ * W) * r) ≤
            Cw * r ^ (-(1 / 2 : ℝ)) * Real.exp (-(c * r)) := by
        have hrn : 0 ≤ r ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hr0.le _
        exact mul_le_mul (mul_le_mul_of_nonneg_right hws_le hrn) hexp_le (Real.exp_nonneg _)
          (mul_nonneg hCw_pos.le hrn)
      have h_in2 : ‖s - 2 * ↑α * rayWeight σ τ ^ 2 * ↑r ^ 2 - z₀ * rayWeight σ τ * ↑r‖ *
          (‖rayWeight σ τ ^ s‖ * r ^ (-(1 / 2 : ℝ)) *
            Real.exp (-(α * (1 - τ ^ 2) * r ^ 2) - (z₀.re + τ * W) * r)) ≤
          (‖s‖ + 8 * α * r ^ 2 + 2 * ‖z₀‖ * r) * (Cw * r ^ (-(1 / 2 : ℝ)) * Real.exp (-(c * r))) :=
        mul_le_mul h_poly h_in1 (by positivity) (by positivity)
      calc
        ‖(σ : ℂ) * I‖ / ‖rayWeight σ τ‖ *
            (‖s - 2 * ↑α * rayWeight σ τ ^ 2 * ↑r ^ 2 - z₀ * rayWeight σ τ * ↑r‖ *
              (‖rayWeight σ τ ^ s‖ * r ^ (-(1 / 2 : ℝ)) *
                Real.exp (-(α * (1 - τ ^ 2) * r ^ 2) - (z₀.re + τ * W) * r)))
          ≤ 2 * ((‖s‖ + 8 * α * r ^ 2 + 2 * ‖z₀‖ * r) * (Cw * r ^ (-(1 / 2 : ℝ)) * Real.exp (-(c * r)))) :=
            mul_le_mul h_pref h_in2 (by positivity) (by norm_num)
        _ = 2 * Cw * (‖s‖ * r ^ (-(1 / 2 : ℝ)) + 8 * α * (r ^ 2 * r ^ (-(1 / 2 : ℝ))) +
              2 * ‖z₀‖ * (r * r ^ (-(1 / 2 : ℝ)))) * Real.exp (-(c * r)) := by ring
        _ = bound r := by rw [hr2, hr1, hr0']
    have hdiff : ∀ᵐ r ∂volume.restrict (Ioi 0), ∀ τ ∈ Ioo ε 1,
        HasDerivAt (fun u => rayIntegrand s z₀ α σ u r) (F' τ r) τ := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with r hr τ _
      exact hasDerivAt_rayIntegrand_tau s z₀ α σ τ hr
    obtain ⟨hF'_int, hH_deriv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      hnhds (Eventually.of_forall hmeas) hF_int hF'_meas hdom hbound_int hdiff
    let G' : ℝ → ℂ := fun r =>
      (s - 2 * (α : ℂ) * rayWeight σ τ₀ ^ 2 * (r : ℂ) ^ 2 - z₀ * rayWeight σ τ₀ * (r : ℂ)) *
        rayIntegrand s z₀ α σ τ₀ r
    have hF'_eq : ∫ r in Ioi 0, F' τ₀ r = ((σ : ℂ) * Complex.I / rayWeight σ τ₀) * ∫ r in Ioi 0, G' r := by
      dsimp [F', G']
      exact integral_const_mul _ _
    have hG'_int : IntegrableOn G' (Ioi 0) := by
      let c_pref : ℂ := (σ : ℂ) * Complex.I / rayWeight σ τ₀
      have hmul_inv : c_pref ≠ 0 := by
        refine div_ne_zero (mul_ne_zero ?_ Complex.I_ne_zero) (rayWeight_ne_zero σ τ₀)
        exact Complex.ofReal_ne_zero.mpr (by intro h0; rw [h0] at hσ; norm_num at hσ)
      have htmp : IntegrableOn (fun x => c_pref⁻¹ * F' τ₀ x) (Ioi 0) := hF'_int.const_mul _
      refine IntegrableOn.congr_fun htmp (fun r _ => ?_) measurableSet_Ioi
      change c_pref⁻¹ * (c_pref * G' r) = G' r
      exact inv_mul_cancel_left₀ hmul_inv (G' r)
    have hprim0 : rayPrim s z₀ α σ τ₀ 0 = 0 := by
      simp [rayPrim, Complex.zero_cpow hs_ne]
    have hcont0 : ContinuousWithinAt (rayPrim s z₀ α σ τ₀) (Ici 0) 0 := by
      rw [ContinuousWithinAt, hprim0]
      refine squeeze_zero_norm' (a := fun r : ℝ => Cw * r ^ (1 / 2 : ℝ)) ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with r hr
        rcases eq_or_lt_of_le (mem_Ici.mp hr) with rfl | hr0
        · simp [hprim0]
        · rw [norm_rayPrim_eq hre α σ τ₀ hσ hr0, hlin τ₀]
          have hw_le : ‖rayWeight σ τ₀ ^ s‖ ≤ Cw :=
            norm_rayWeight_cpow_le hre σ τ₀ hσ (by linarith [hτ₀.1]) hτ₀.2.le
          have hexp_le1 : Real.exp (-(α * (1 - τ₀ ^ 2) * r ^ 2) - (z₀.re + τ₀ * W) * r) ≤ 1 := by
            apply Real.exp_le_one_iff.mpr
            have h1mt : 0 ≤ 1 - τ₀ ^ 2 := by nlinarith [hτ₀.1, hτ₀.2]
            have h1 : 0 ≤ α * (1 - τ₀ ^ 2) * r ^ 2 := by positivity
            have h2 : 0 ≤ (z₀.re + τ₀ * W) * r := mul_nonneg (by nlinarith [hz_re, hτ₀.1, hW]) hr0.le
            linarith
          have hrp_nn : 0 ≤ r ^ (1 / 2 : ℝ) := Real.rpow_nonneg hr0.le _
          calc
            ‖rayWeight σ τ₀ ^ s‖ * r ^ (1 / 2 : ℝ) *
                Real.exp (-(α * (1 - τ₀ ^ 2) * r ^ 2) - (z₀.re + τ₀ * W) * r)
              ≤ (Cw * r ^ (1 / 2 : ℝ)) * 1 :=
                mul_le_mul (mul_le_mul_of_nonneg_right hw_le hrp_nn) hexp_le1 (Real.exp_nonneg _)
                  (mul_nonneg hCw_pos.le hrp_nn)
            _ = Cw * r ^ (1 / 2 : ℝ) := mul_one _
      · have h_rpow : Tendsto (fun r : ℝ => Cw * r ^ (1 / 2 : ℝ)) (𝓝 0) (𝓝 0) := by
          simpa using (Real.continuousAt_rpow_const 0 (1 / 2) (Or.inr (by norm_num))).tendsto.const_mul Cw
        exact h_rpow.mono_left nhdsWithin_le_nhds
    have htend_top : Tendsto (rayPrim s z₀ α σ τ₀) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun r : ℝ => Cw * (r ^ (1 / 2 : ℝ) * Real.exp (-(c * r)))) ?_ ?_
      · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with r hr0
        rw [norm_rayPrim_eq hre α σ τ₀ hσ hr0, hlin τ₀]
        have hw_le : ‖rayWeight σ τ₀ ^ s‖ ≤ Cw :=
          norm_rayWeight_cpow_le hre σ τ₀ hσ (by linarith [hτ₀.1]) hτ₀.2.le
        have hexp_le : Real.exp (-(α * (1 - τ₀ ^ 2) * r ^ 2) - (z₀.re + τ₀ * W) * r) ≤ Real.exp (-(c * r)) := by
          apply Real.exp_le_exp.mpr
          have h1mt : 0 ≤ 1 - τ₀ ^ 2 := by nlinarith [hτ₀.1, hτ₀.2]
          have h1 : 0 ≤ α * (1 - τ₀ ^ 2) * r ^ 2 := by positivity
          have h2 : c ≤ z₀.re + τ₀ * W := by dsimp [c, ε]; nlinarith [hτ₀.1, hW, hz_re]
          have h3 : c * r ≤ (z₀.re + τ₀ * W) * r := mul_le_mul_of_nonneg_right h2 (le_of_lt hr0)
          linarith
        have hrp_nn : 0 ≤ r ^ (1 / 2 : ℝ) := Real.rpow_nonneg (le_of_lt hr0) _
        calc
          ‖rayWeight σ τ₀ ^ s‖ * r ^ (1 / 2 : ℝ) *
              Real.exp (-(α * (1 - τ₀ ^ 2) * r ^ 2) - (z₀.re + τ₀ * W) * r)
            ≤ (Cw * r ^ (1 / 2 : ℝ)) * Real.exp (-(c * r)) :=
              mul_le_mul (mul_le_mul_of_nonneg_right hw_le hrp_nn) hexp_le (Real.exp_nonneg _)
                (mul_nonneg hCw_pos.le hrp_nn)
          _ = Cw * (r ^ (1 / 2 : ℝ) * Real.exp (-(c * r))) := by ring
      · simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) c hc).const_mul Cw
    have hftc := integral_Ioi_of_hasDerivAt_of_tendsto hcont0
      (fun r hr => hasDerivAt_rayPrim_r s z₀ hs_ne α σ τ₀ hr) hG'_int htend_top
    rw [hprim0, sub_zero] at hftc
    rw [hF'_eq, hftc, mul_zero] at hH_deriv
    exact hH_deriv
  have hconst_Ioo : ∀ τ ∈ Ioo (0 : ℝ) 1, H τ = H (1 / 2) := by
    intro τ hτ
    refine IsOpen.is_const_of_deriv_eq_zero isOpen_Ioo (convex_Ioo 0 1).isPreconnected
      (fun u hu => (hderiv_zero u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => (hderiv_zero u hu).deriv) hτ ⟨by norm_num, by norm_num⟩
  have htend0 : Tendsto H (𝓝[>] 0) (𝓝 (H 0)) := by
    let c₀ : ℝ := if 0 < α then (3 / 8) * α else z₀.re
    have hc₀ : 0 < c₀ := by
      dsimp [c₀]
      split_ifs with hα_pos
      · positivity
      · rcases h0_decay with h1 | h2
        · exact absurd h1 hα_pos
        · exact h2
    let C₀ : ℝ := Cw * Real.exp (α / 4)
    have hdom0 : IntegrableOn (fun r : ℝ => C₀ * (r ^ (1 / 2 - 1 : ℝ) * Real.exp (-(c₀ * r)))) (Ioi 0) :=
      (integrableOn_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 1 / 2) hc₀).const_mul C₀
    refine tendsto_integral_filter_of_dominated_convergence _
      (Eventually.of_forall hmeas) ?_ hdom0 ?_
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with τ hτ
      rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with r hr
      have hr0 : 0 < r := hr
      rw [norm_rayIntegrand_eq hre α σ τ hσ hr0, hlin τ]
      have hw_le : ‖rayWeight σ τ ^ s‖ ≤ Cw :=
        norm_rayWeight_cpow_le hre σ τ hσ (by linarith [hτ.1]) (by linarith [hτ.2])
      have hexp_le : Real.exp (-(α * (1 - τ ^ 2) * r ^ 2) - (z₀.re + τ * W) * r) ≤
          Real.exp (α / 4) * Real.exp (-(c₀ * r)) := by
        dsimp [c₀]
        split_ifs with hα_pos
        · have h1 : (3 / 8) * α * r ^ 2 ≤ α * (1 - τ ^ 2) * r ^ 2 := by
            have h1t : (3 / 8 : ℝ) ≤ 1 - τ ^ 2 := by nlinarith [hτ.1, hτ.2]
            have h1a : 3 / 8 * α ≤ α * (1 - τ ^ 2) := by
              simpa [mul_comm] using mul_le_mul_of_nonneg_left h1t hα_pos.le
            exact mul_le_mul_of_nonneg_right h1a (sq_nonneg r)
          have h2 : 0 ≤ (z₀.re + τ * W) * r := mul_nonneg (by nlinarith [hz_re, hτ.1, hW]) hr0.le
          calc
            Real.exp (-(α * (1 - τ ^ 2) * r ^ 2) - (z₀.re + τ * W) * r)
              ≤ Real.exp (-((3 / 8 * α) * r ^ 2)) := Real.exp_le_exp.mpr (by linarith)
            _ ≤ Real.exp ((3 / 8 * α) / 4) * Real.exp (-((3 / 8 * α) * r)) :=
                exp_neg_mul_sq_le (3 / 8 * α) r (by positivity)
            _ ≤ Real.exp (α / 4) * Real.exp (-((3 / 8 * α) * r)) := by
                gcongr; linarith
        · have hα0 : α = 0 := le_antisymm (not_lt.mp hα_pos) hα
          subst hα0
          simp only [zero_mul, neg_zero, zero_sub, zero_div, Real.exp_zero, one_mul]
          apply Real.exp_le_exp.mpr
          have htr : 0 ≤ τ * W * r := mul_nonneg (mul_nonneg hτ.1.le hW.le) hr0.le
          linarith
      have hr0' : r ^ (-(1 / 2 : ℝ)) = r ^ (1 / 2 - 1 : ℝ) := by norm_num
      rw [hr0']
      have hrp_nn : 0 ≤ r ^ (1 / 2 - 1 : ℝ) := Real.rpow_nonneg hr0.le _
      calc
        ‖rayWeight σ τ ^ s‖ * r ^ (1 / 2 - 1 : ℝ) *
            Real.exp (-(α * (1 - τ ^ 2) * r ^ 2) - (z₀.re + τ * W) * r)
          ≤ (Cw * r ^ (1 / 2 - 1 : ℝ)) * (Real.exp (α / 4) * Real.exp (-(c₀ * r))) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hw_le hrp_nn) hexp_le (by positivity)
              (mul_nonneg hCw_pos.le hrp_nn)
        _ = C₀ * (r ^ (1 / 2 - 1 : ℝ) * Real.exp (-(c₀ * r))) := by dsimp [C₀]; ring
    · rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with r hr
      exact (hasDerivAt_rayIntegrand_tau s z₀ α σ 0 hr).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have htend1 : Tendsto H (𝓝[<] 1) (𝓝 (H 1)) := by
    let c₁ : ℝ := (1 / 2) * W
    have hc₁ : 0 < c₁ := by dsimp [c₁]; positivity
    have hdom1 : IntegrableOn (fun r : ℝ => Cw * (r ^ (1 / 2 - 1 : ℝ) * Real.exp (-(c₁ * r)))) (Ioi 0) :=
      (integrableOn_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 1 / 2) hc₁).const_mul Cw
    refine tendsto_integral_filter_of_dominated_convergence _
      (Eventually.of_forall hmeas) ?_ hdom1 ?_
    · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with τ hτ
      rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with r hr
      have hr0 : 0 < r := hr
      rw [norm_rayIntegrand_eq hre α σ τ hσ hr0, hlin τ]
      have hw_le : ‖rayWeight σ τ ^ s‖ ≤ Cw :=
        norm_rayWeight_cpow_le hre σ τ hσ (by linarith [hτ.1]) hτ.2.le
      have hexp_le : Real.exp (-(α * (1 - τ ^ 2) * r ^ 2) - (z₀.re + τ * W) * r) ≤ Real.exp (-(c₁ * r)) := by
        apply Real.exp_le_exp.mpr
        have h1mt : 0 ≤ 1 - τ ^ 2 := by nlinarith [hτ.1, hτ.2]
        have h1 : 0 ≤ α * (1 - τ ^ 2) * r ^ 2 := by positivity
        have h2 : c₁ ≤ z₀.re + τ * W := by dsimp [c₁]; nlinarith [hz_re, hτ.1, hW]
        have h3 : c₁ * r ≤ (z₀.re + τ * W) * r := mul_le_mul_of_nonneg_right h2 hr0.le
        linarith
      have hr0' : r ^ (-(1 / 2 : ℝ)) = r ^ (1 / 2 - 1 : ℝ) := by norm_num
      rw [hr0']
      have hrp_nn : 0 ≤ r ^ (1 / 2 - 1 : ℝ) := Real.rpow_nonneg hr0.le _
      calc
        ‖rayWeight σ τ ^ s‖ * r ^ (1 / 2 - 1 : ℝ) *
            Real.exp (-(α * (1 - τ ^ 2) * r ^ 2) - (z₀.re + τ * W) * r)
          ≤ (Cw * r ^ (1 / 2 - 1 : ℝ)) * Real.exp (-(c₁ * r)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hw_le hrp_nn) hexp_le (Real.exp_nonneg _)
              (mul_nonneg hCw_pos.le hrp_nn)
        _ = Cw * (r ^ (1 / 2 - 1 : ℝ) * Real.exp (-(c₁ * r))) := by ring
    · rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with r hr
      exact (hasDerivAt_rayIntegrand_tau s z₀ α σ 1 hr).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h0_eq : H 0 = H (1 / 2) := by
    have h_ev : H =ᶠ[𝓝[>] 0] fun _ => H (1 / 2) := by
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with τ hτ
      exact hconst_Ioo τ hτ
    exact tendsto_nhds_unique htend0 (tendsto_const_nhds.congr' h_ev.symm)
  have h1_eq : H 1 = H (1 / 2) := by
    have h_ev : H =ᶠ[𝓝[<] 1] fun _ => H (1 / 2) := by
      filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with τ hτ
      exact hconst_Ioo τ hτ
    exact tendsto_nhds_unique htend1 (tendsto_const_nhds.congr' h_ev.symm)
  exact h0_eq.trans h1_eq.symm

private lemma gamma_ray_eq {s : ℂ} (hre : s.re = 1 / 2) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    ∫ v : ℝ in Ioi 0, (v : ℂ) ^ (s - 1) * Complex.exp (-((1 - (σ : ℂ) * Complex.I) * (v : ℂ))) =
      rayWeight σ 1 ^ s * ((1 / 2 : ℂ) ^ s * Complex.Gamma s) := by
  let z₀ : ℂ := 1 - (σ : ℂ) * Complex.I
  have hz_re : 0 ≤ z₀.re := by simp [z₀]
  have hW : 0 < -σ * z₀.im := by
    have : -σ * z₀.im = σ ^ 2 := by simp [z₀]; ring
    rw [this, hσ]; norm_num
  have hrot := ray_rotation_eq (s := s) (z₀ := z₀) (α := 0) (σ := σ)
    hre (by norm_num) hσ hz_re hW (Or.inr (by simp [z₀]))
  have h0 : (∫ v : ℝ in Ioi 0, rayIntegrand s z₀ 0 σ 0 v) =
      ∫ v : ℝ in Ioi 0, (v : ℂ) ^ (s - 1) * Complex.exp (-((1 - (σ : ℂ) * Complex.I) * (v : ℂ))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    simp [rayIntegrand, rayExp, rayWeight, z₀]
  have h1 : (∫ v : ℝ in Ioi 0, rayIntegrand s z₀ 0 σ 1 v) =
      rayWeight σ 1 ^ s * ∫ v : ℝ in Ioi 0, (v : ℂ) ^ (s - 1) * (Real.exp (-(2 * v)) : ℂ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    have hσc : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσ
    have hz_prod : z₀ * rayWeight σ 1 = 2 := by
      simp only [z₀, rayWeight, one_mul]
      calc
        (1 - (σ : ℂ) * I) * (1 + (σ : ℂ) * I) = 1 - (σ : ℂ) ^ 2 * I ^ 2 := by ring
        _ = 2 := by rw [Complex.I_sq, hσc]; ring
    dsimp only [rayIntegrand, rayExp]
    rw [Complex.ofReal_zero, zero_mul, zero_mul, neg_zero, zero_sub, hz_prod]
    rw [Complex.ofReal_exp]
    push_cast
    ring_nf
  have hgam := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := s) (r := 2)
    (by linarith : 0 < s.re) (by norm_num : (0 : ℝ) < 2)
  rw [h0, h1] at hrot
  rw [hrot]
  simpa using congrArg (rayWeight σ 1 ^ s * ·) hgam

private lemma norm_gamma_half_add_it (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ =
      Real.sqrt (Real.pi / Real.cosh (Real.pi * t)) := by
  let s : ℂ := (1 / 2 : ℂ) + (t : ℝ) * Complex.I
  have hconj : 1 - s = starRingEnd ℂ s := by
    simp [s, Complex.ext_iff]
    norm_num
  have href := Complex.Gamma_mul_Gamma_one_sub s
  rw [hconj, Complex.Gamma_conj] at href
  have hsin : Complex.sin (↑Real.pi * s) = (Real.cosh (Real.pi * t) : ℂ) := by
    have hpis : (↑Real.pi : ℂ) * s = ↑(Real.pi / 2) + (↑(Real.pi * t) : ℂ) * Complex.I := by
      simp [s]; ring
    rw [hpis, Complex.sin_add]
    have hs1 : Complex.sin ↑(Real.pi / 2) = 1 := by rw [← Complex.ofReal_sin, Real.sin_pi_div_two, Complex.ofReal_one]
    have hc1 : Complex.cos ↑(Real.pi / 2) = 0 := by rw [← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero]
    rw [hs1, hc1, one_mul, zero_mul, add_zero, Complex.cos_mul_I]
    simp [Real.cosh_eq, Complex.cosh]
  rw [hsin] at href
  have hnorm_prod : ‖Complex.Gamma s * (starRingEnd ℂ) (Complex.Gamma s)‖ =
      Real.pi / Real.cosh (Real.pi * t) := by
    have hpos : 0 < Real.pi / Real.cosh (Real.pi * t) :=
      div_pos Real.pi_pos (Real.cosh_pos _)
    have href' : Complex.Gamma s * (starRingEnd ℂ) (Complex.Gamma s) =
        ((Real.pi / Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
      simpa [Complex.ofReal_div] using href
    rw [href', Complex.norm_real, Real.norm_of_nonneg hpos.le]
  rw [norm_mul, RCLike.norm_conj, ← sq] at hnorm_prod
  calc
    ‖Complex.Gamma s‖ = Real.sqrt (‖Complex.Gamma s‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (Real.pi / Real.cosh (Real.pi * t)) := by rw [hnorm_prod]

private lemma arg_rayWeight_one {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    (rayWeight σ 1).arg = σ * (Real.pi / 4) := by
  have hpi4_pos : -(Real.pi) < Real.pi / 4 ∧ Real.pi / 4 ≤ Real.pi :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hpi4_neg : -(Real.pi) < -(Real.pi / 4) ∧ -(Real.pi / 4) ≤ Real.pi :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rcases hσ with rfl | rfl
  · have heq : rayWeight 1 1 = (Real.sqrt 2 : ℂ) *
        (Complex.cos ↑(Real.pi / 4) + Complex.sin ↑(Real.pi / 4) * Complex.I) := by
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
      simp only [rayWeight, mul_one, Complex.ofReal_one]
      apply Complex.ext <;> simp <;>
        nlinarith [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [heq, Complex.arg_mul_cos_add_sin_mul_I (Real.sqrt_pos.mpr (by norm_num)) hpi4_pos]
    ring
  · have heq : rayWeight (-1) 1 = (Real.sqrt 2 : ℂ) *
        (Complex.cos ↑(-(Real.pi / 4)) + Complex.sin ↑(-(Real.pi / 4)) * Complex.I) := by
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
        Real.cos_pi_div_four, Real.sin_pi_div_four]
      simp only [rayWeight, one_mul, Complex.ofReal_neg, Complex.ofReal_one]
      apply Complex.ext <;> simp <;>
        nlinarith [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [heq, Complex.arg_mul_cos_add_sin_mul_I (Real.sqrt_pos.mpr (by norm_num)) hpi4_neg]
    ring

private lemma norm_rayWeight_one_cpow (t : ℝ) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ‖rayWeight σ 1 ^ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ =
      (2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (-(σ * (Real.pi / 4) * t)) := by
  let s : ℂ := (1 / 2 : ℂ) + (t : ℝ) * Complex.I
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  rw [Complex.norm_cpow_of_ne_zero (rayWeight_ne_zero σ 1) s]
  have hs_re : s.re = 1 / 2 := by simp [s]
  have hs_im : s.im = t := by simp [s]
  rw [hs_re, hs_im, arg_rayWeight_one hσ]
  have hnorm : ‖rayWeight σ 1‖ = Real.sqrt 2 := by
    have hsq := norm_rayWeight_sq σ 1 hσ2
    rw [← Real.sqrt_sq (norm_nonneg _), hsq]
    norm_num
  have hrpow : (Real.sqrt 2) ^ (1 / 2 : ℝ) = (2 : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [hnorm, hrpow, div_eq_mul_inv, ← Real.exp_neg]

private def J_int (σ W : ℝ) (s : ℂ) : ℂ :=
  ∫ v : ℝ in Ioi 0,
    (v : ℂ) ^ (s - 1) * Complex.exp (-((1 - (σ : ℂ) * Complex.I) * (v : ℂ))) *
      Complex.exp (-Complex.I * ↑(σ * (v / W) ^ 2))

private def J_inf (σ : ℝ) (s : ℂ) : ℂ :=
  ∫ v : ℝ in Ioi 0, (v : ℂ) ^ (s - 1) * Complex.exp (-((1 - (σ : ℂ) * Complex.I) * (v : ℂ)))

private lemma norm_mellin_gauss_eq {δ : ℝ} (_hδ : 1 ≤ |δ|) (t : ℝ) (_hpos : 0 < |δ|) :
    let σ : ℝ := if 0 ≤ δ then 1 else -1
    let W : ℝ := 2 * Real.pi * |δ|
    let s : ℂ := (1 / 2 : ℂ) + (t : ℝ) * Complex.I
    ‖mellin (fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ))) s‖ =
      W ^ (-(1 / 2 : ℝ)) * ‖rayWeight σ 1 ^ s‖ * ‖J_int σ W s‖ := by
  intro σ W s
  have hσ_cases : σ = 1 ∨ σ = -1 := by
    dsimp [σ]; split_ifs <;> [exact Or.inl rfl; exact Or.inr rfl]
  have hσ2 : σ ^ 2 = 1 := by rcases hσ_cases with h | h <;> simp [h]
  have hσc : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσ2
  have hσ_abs : σ * |δ| = δ := by
    dsimp [σ]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  have hσW : σ * W = 2 * Real.pi * δ := by
    dsimp [W]; linear_combination 2 * Real.pi * hσ_abs
  have hW_pos : 0 < W := by dsimp [W]; positivity
  have hs_re : s.re = 1 / 2 := by simp [s]
  let z₀ : ℂ := -Complex.I * ↑(σ * W)
  have hz_re : 0 ≤ z₀.re := by simp [z₀]
  have hz_W : 0 < -σ * z₀.im := by
    have : -σ * z₀.im = σ ^ 2 * W := by simp [z₀]; ring
    rw [this, hσ2, one_mul]; exact hW_pos
  have hrot := ray_rotation_eq (s := s) (z₀ := z₀) (α := 1 / 2) (σ := σ)
    hs_re (by norm_num) hσ2 hz_re hz_W (Or.inl (by norm_num))
  have hmellin : mellin (fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ))) s =
      ∫ r : ℝ in Ioi 0, rayIntegrand s z₀ (1 / 2) σ 0 r := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    dsimp only [smul_eq_mul, rayIntegrand, rayExp, rayWeight, z₀]
    rw [hσW, zero_mul, Complex.ofReal_zero, zero_mul, add_zero, Complex.one_cpow, one_pow,
      mul_one, one_mul, mul_one, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hmellin, hrot]
  let g : ℝ → ℂ := fun v =>
    (rayWeight σ 1 ^ s * (W : ℂ) ^ (1 - s)) *
      ((v : ℂ) ^ (s - 1) * Complex.exp (-((1 - (σ : ℂ) * Complex.I) * (v : ℂ))) *
        Complex.exp (-Complex.I * ↑(σ * (v / W) ^ 2)))
  have h_integrand_eq : EqOn (fun r : ℝ => rayIntegrand s z₀ (1 / 2) σ 1 r)
      (fun r : ℝ => g (W * r)) (Ioi 0) := by
    intro r hr
    have hr0 : 0 < r := hr
    dsimp only [g, rayIntegrand, rayExp]
    have hWr_cpow : ((W * r : ℝ) : ℂ) ^ (s - 1) = (W : ℂ) ^ (s - 1) * (r : ℂ) ^ (s - 1) := by
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hW_pos.le hr0.le]
    have hW_cancel : (W : ℂ) ^ (1 - s) * (W : ℂ) ^ (s - 1) = 1 := by
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hW_pos.ne')]
      have : (1 - s) + (s - 1) = 0 := by ring
      rw [this, Complex.cpow_zero]
    have hvW : W * r / W = r := mul_div_cancel_left₀ r hW_pos.ne'
    have hexp_eq : -((1 - (σ : ℂ) * I) * ↑(W * r)) + (-I * ↑(σ * (W * r / W) ^ 2)) =
        -(((1 / 2 : ℝ) : ℂ) * rayWeight σ 1 ^ 2 * (r : ℂ) ^ 2) - z₀ * rayWeight σ 1 * (r : ℂ) := by
      rw [hvW]
      have hw1_sq : rayWeight σ 1 ^ 2 = 2 * (σ : ℂ) * I := by
        simp only [rayWeight, one_mul]
        calc
          (1 + (σ : ℂ) * I) ^ 2 = 1 + 2 * (σ : ℂ) * I + (σ : ℂ) ^ 2 * I ^ 2 := by ring
          _ = 2 * (σ : ℂ) * I := by rw [Complex.I_sq, hσc]; ring
      have hz_w1 : z₀ * rayWeight σ 1 = (1 - (σ : ℂ) * I) * (W : ℂ) := by
        simp only [z₀, rayWeight, one_mul]
        push_cast
        calc
          -I * ((σ : ℂ) * (W : ℂ)) * (1 + (σ : ℂ) * I)
              = (-(σ : ℂ) ^ 2 * I ^ 2 - (σ : ℂ) * I) * (W : ℂ) := by ring
          _ = (1 - (σ : ℂ) * I) * (W : ℂ) := by rw [Complex.I_sq, hσc]; ring
      rw [hw1_sq, hz_w1]
      push_cast
      ring
    rw [hWr_cpow, mul_assoc ((W : ℂ) ^ (s - 1) * (r : ℂ) ^ (s - 1)), ← Complex.exp_add, hexp_eq]
    calc
      rayWeight σ 1 ^ s * ↑r ^ (s - 1) *
          cexp (-(↑(1 / 2 : ℝ) * rayWeight σ 1 ^ 2 * ↑r ^ 2) - z₀ * rayWeight σ 1 * ↑r)
        = (rayWeight σ 1 ^ s * ((W : ℂ) ^ (1 - s) * (W : ℂ) ^ (s - 1))) *
            (↑r ^ (s - 1) *
              cexp (-(↑(1 / 2 : ℝ) * rayWeight σ 1 ^ 2 * ↑r ^ 2) - z₀ * rayWeight σ 1 * ↑r)) := by
          rw [hW_cancel, mul_one, mul_assoc]
      _ = rayWeight σ 1 ^ s * (W : ℂ) ^ (1 - s) *
            ((W : ℂ) ^ (s - 1) * ↑r ^ (s - 1) *
              cexp (-(↑(1 / 2 : ℝ) * rayWeight σ 1 ^ 2 * ↑r ^ 2) - z₀ * rayWeight σ 1 * ↑r)) := by
          ring
  rw [setIntegral_congr_fun measurableSet_Ioi h_integrand_eq]
  rw [integral_comp_mul_left_Ioi g 0 hW_pos, mul_zero]
  have hg_pull : ∫ x : ℝ in Ioi 0, g x = (rayWeight σ 1 ^ s * (W : ℂ) ^ (1 - s)) * J_int σ W s := by
    dsimp [g, J_int]
    exact integral_const_mul _ _
  rw [hg_pull, norm_smul, norm_mul, norm_mul]
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hW_pos.le)]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hW_pos]
  have h1ms : (1 - s).re = 1 / 2 := by simp [s]; norm_num
  rw [h1ms]
  have hW_rpow : W⁻¹ * W ^ (1 / 2 : ℝ) = W ^ (-(1 / 2 : ℝ)) := by
    calc
      W⁻¹ * W ^ (1 / 2 : ℝ) = W ^ (-1 : ℝ) * W ^ (1 / 2 : ℝ) := by rw [Real.rpow_neg_one]
      _ = W ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hW_pos]; norm_num
  calc
    W⁻¹ * (‖rayWeight σ 1 ^ s‖ * W ^ (1 / 2 : ℝ) * ‖J_int σ W s‖)
        = (W⁻¹ * W ^ (1 / 2 : ℝ)) * ‖rayWeight σ 1 ^ s‖ * ‖J_int σ W s‖ := by ring
    _ = W ^ (-(1 / 2 : ℝ)) * ‖rayWeight σ 1 ^ s‖ * ‖J_int σ W s‖ := by rw [hW_rpow]

private lemma norm_J_sub_J_inf_le {σ W : ℝ} (hσ : σ = 1 ∨ σ = -1) (hW : 2 * Real.pi ≤ W)
    {s : ℂ} (hre : s.re = 1 / 2) :
    ‖J_int σ W s - J_inf σ s‖ ≤ 3 * Real.sqrt Real.pi / (16 * Real.pi ^ 2) := by
  have hW_pos : 0 < W := lt_of_lt_of_le (by positivity) hW
  have hσ_abs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  let f1 : ℝ → ℂ := fun v =>
    (v : ℂ) ^ (s - 1) * Complex.exp (-((1 - (σ : ℂ) * Complex.I) * (v : ℂ))) *
      Complex.exp (-Complex.I * ↑(σ * (v / W) ^ 2))
  let f2 : ℝ → ℂ := fun v =>
    (v : ℂ) ^ (s - 1) * Complex.exp (-((1 - (σ : ℂ) * Complex.I) * (v : ℂ)))
  have hf2_meas : AEStronglyMeasurable f2 (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul ?_ (Continuous.continuousOn (by fun_prop))
    intro v hv
    exact (continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hv))).continuousWithinAt
  have hf1_meas : AEStronglyMeasurable f1 (volume.restrict (Ioi 0)) :=
    hf2_meas.mul (Continuous.continuousOn (by fun_prop) |>.aestronglyMeasurable measurableSet_Ioi)
  have hdom_base : IntegrableOn (fun v : ℝ => Real.exp (-v) * v ^ (1 / 2 - 1 : ℝ)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 1 / 2)
  have hf2_norm : ∀ v > (0 : ℝ), ‖f2 v‖ = Real.exp (-v) * v ^ (1 / 2 - 1 : ℝ) := by
    intro v hv
    dsimp [f2]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv, Complex.norm_exp]
    have hs1 : (s - 1).re = 1 / 2 - 1 := by simp [hre]
    have hexp_re : (-((1 - (σ : ℂ) * Complex.I) * (v : ℂ))).re = -v := by simp
    rw [hs1, hexp_re, mul_comm]
  have hf2_int : IntegrableOn f2 (Ioi 0) := by
    refine hdom_base.mono' hf2_meas ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with v hv
    rw [hf2_norm v hv]
  have hf1_int : IntegrableOn f1 (Ioi 0) := by
    refine hdom_base.mono' hf1_meas ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with v hv
    dsimp [f1]
    rw [norm_mul, hf2_norm v hv]
    have hexp1 : ‖Complex.exp (-Complex.I * ↑(σ * (v / W) ^ 2))‖ = 1 := by
      have : -Complex.I * ↑(σ * (v / W) ^ 2) = ↑(-(σ * (v / W) ^ 2)) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [hexp1, mul_one]
  have hsub_eq : J_int σ W s - J_inf σ s = ∫ v : ℝ in Ioi 0, (f1 v - f2 v) := by
    dsimp [J_int, J_inf, f1, f2]
    exact (integral_sub hf1_int hf2_int).symm
  let g_bound : ℝ → ℝ := fun v => (1 / W ^ 2) * (Real.exp (-v) * v ^ (5 / 2 - 1 : ℝ))
  have hg_int : IntegrableOn g_bound (Ioi 0) :=
    (Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 5 / 2)).const_mul (1 / W ^ 2)
  have hpt : ∀ᵐ v ∂volume.restrict (Ioi 0), ‖f1 v - f2 v‖ ≤ g_bound v := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with v hv
    have hv0 : 0 < v := hv
    have hfac : f1 v - f2 v = f2 v * (Complex.exp (Complex.I * ↑(-(σ * (v / W) ^ 2))) - 1) := by
      dsimp [f1, f2]
      have : -Complex.I * ↑(σ * (v / W) ^ 2) = Complex.I * ↑(-(σ * (v / W) ^ 2)) := by
        push_cast; ring
      rw [this]; ring
    rw [hfac, norm_mul, hf2_norm v hv0]
    have hexp_sub : ‖Complex.exp (Complex.I * ↑(-(σ * (v / W) ^ 2))) - 1‖ ≤ v ^ 2 / W ^ 2 := by
      calc
        ‖Complex.exp (Complex.I * ↑(-(σ * (v / W) ^ 2))) - 1‖
          ≤ ‖-(σ * (v / W) ^ 2)‖ := norm_exp_I_mul_ofReal_sub_one_le
        _ = |σ| * (|v| / |W|) ^ 2 := by rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_pow, abs_div]
        _ = v ^ 2 / W ^ 2 := by rw [hσ_abs, one_mul, abs_of_pos hv0, abs_of_pos hW_pos, div_pow]
    have hv_rpow : v ^ (1 / 2 - 1 : ℝ) * v ^ 2 = v ^ (5 / 2 - 1 : ℝ) := by
      rw [← Real.rpow_natCast v 2, ← Real.rpow_add hv0]; norm_num
    calc
      Real.exp (-v) * v ^ (1 / 2 - 1 : ℝ) * ‖Complex.exp (Complex.I * ↑(-(σ * (v / W) ^ 2))) - 1‖
        ≤ Real.exp (-v) * v ^ (1 / 2 - 1 : ℝ) * (v ^ 2 / W ^ 2) := by
          exact mul_le_mul_of_nonneg_left hexp_sub (by positivity)
      _ = (1 / W ^ 2) * (Real.exp (-v) * (v ^ (1 / 2 - 1 : ℝ) * v ^ 2)) := by ring
      _ = g_bound v := by dsimp [g_bound]; rw [hv_rpow]
  have hnorm_int : ‖J_int σ W s - J_inf σ s‖ ≤ ∫ v : ℝ in Ioi 0, g_bound v := by
    rw [hsub_eq]
    exact le_trans (norm_integral_le_integral_norm _)
      (integral_mono_ae (hf1_int.sub hf2_int).norm hg_int hpt)
  have hgam52 : ∫ v : ℝ in Ioi 0, g_bound v = (1 / W ^ 2) * ((3 / 4) * Real.sqrt Real.pi) := by
    dsimp [g_bound]
    rw [integral_const_mul, ← Real.Gamma_eq_integral (by norm_num : (0 : ℝ) < 5 / 2)]
    have hg1 : Real.Gamma (5 / 2) = (3 / 2) * Real.Gamma (3 / 2) := by
      rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
    have hg2 : Real.Gamma (3 / 2) = (1 / 2) * Real.Gamma (1 / 2) := by
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
    rw [hg1, hg2, Real.Gamma_one_half_eq]
    ring
  rw [hgam52] at hnorm_int
  have hW_sq : 1 / W ^ 2 ≤ 1 / (4 * Real.pi ^ 2) := by
    have h4 : 4 * Real.pi ^ 2 ≤ W ^ 2 := by
      have : (2 * Real.pi) ^ 2 ≤ W ^ 2 := pow_le_pow_left₀ (by positivity) hW 2
      linarith
    exact one_div_le_one_div_of_le (by positivity) h4
  calc
    ‖J_int σ W s - J_inf σ s‖ ≤ (1 / W ^ 2) * ((3 / 4) * Real.sqrt Real.pi) := hnorm_int
    _ ≤ (1 / (4 * Real.pi ^ 2)) * ((3 / 4) * Real.sqrt Real.pi) :=
        mul_le_mul_of_nonneg_right hW_sq (by positivity)
    _ = 3 * Real.sqrt Real.pi / (16 * Real.pi ^ 2) := by ring

private lemma norm_J_inf_eq {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (t : ℝ) :
    ‖J_inf σ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ =
      Real.sqrt Real.pi *
        ((2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (-(σ * (Real.pi / 4) * t)) /
          Real.sqrt (Real.cosh (Real.pi * t))) := by
  let s : ℂ := (1 / 2 : ℂ) + (t : ℝ) * Complex.I
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hs_re : s.re = 1 / 2 := by simp [s]
  unfold J_inf
  rw [gamma_ray_eq hs_re hσ2, norm_mul, norm_mul]
  rw [norm_rayWeight_one_cpow t hσ, norm_gamma_half_add_it t]
  have hhalf_cpow : ‖(1 / 2 : ℂ) ^ s‖ = (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have heq : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [heq, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), hs_re]
    rw [show (1 / 2 : ℝ) = 2 ^ (-1 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [hhalf_cpow, Real.sqrt_div Real.pi_pos.le]
  have h2_comb : (2 : ℝ) ^ (1 / 4 : ℝ) * (2 : ℝ) ^ (-(1 / 2 : ℝ)) = (2 : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  calc
    (2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (-(σ * (Real.pi / 4) * t)) *
        ((2 : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.sqrt Real.pi / Real.sqrt (Real.cosh (Real.pi * t))))
      = Real.sqrt Real.pi *
          (((2 : ℝ) ^ (1 / 4 : ℝ) * (2 : ℝ) ^ (-(1 / 2 : ℝ))) *
            Real.exp (-(σ * (Real.pi / 4) * t)) / Real.sqrt (Real.cosh (Real.pi * t))) := by ring
    _ = Real.sqrt Real.pi *
          ((2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (-(σ * (Real.pi / 4) * t)) /
            Real.sqrt (Real.cosh (Real.pi * t))) := by rw [h2_comb]

private lemma exp_bounds_aux :
    Real.exp (2 * Real.pi) < 570 ∧ 20 < Real.exp Real.pi ∧ (2 : ℝ) / 5 < Real.exp (-(Real.pi / 4)) := by
  have hpi_lo : (3.14 : ℝ) < Real.pi := lt_trans (by norm_num) Real.pi_gt_d20
  have hpi_hi : Real.pi < (3.15 : ℝ) := lt_trans Real.pi_lt_d20 (by norm_num)
  have he_lo : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have he_hi : Real.exp 1 < (2.719 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · have h2pi : 2 * Real.pi < 19 / 3 := by linarith
    have hexp_lt : Real.exp (2 * Real.pi) < Real.exp (19 / 3) := Real.exp_lt_exp.mpr h2pi
    have hpow3 : (Real.exp (19 / 3)) ^ 3 < (570 : ℝ) ^ 3 := by
      have h19 : (Real.exp (19 / 3)) ^ 3 = (Real.exp 1) ^ 19 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1; norm_num
      rw [h19]
      calc
        (Real.exp 1) ^ 19 < (2.719 : ℝ) ^ 19 := pow_lt_pow_left₀ he_hi (Real.exp_nonneg _) (by norm_num)
        _ < (570 : ℝ) ^ 3 := by norm_num
    have h570 : Real.exp (19 / 3) < 570 := by
      by_contra hge
      push Not at hge
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 570) hge 3
      linarith [hpow3]
    exact lt_trans hexp_lt h570
  · have h3 : Real.exp 3 < Real.exp Real.pi := Real.exp_lt_exp.mpr (by linarith)
    have he3 : (20 : ℝ) < Real.exp 3 := by
      have : Real.exp 3 = (Real.exp 1) ^ 3 := by
        rw [← Real.exp_nat_mul]; congr 1; norm_num
      rw [this]
      calc
        (20 : ℝ) < (2.718 : ℝ) ^ 3 := by norm_num
        _ < (Real.exp 1) ^ 3 := pow_lt_pow_left₀ he_lo (by norm_num) (by norm_num)
    exact lt_trans he3 h3
  · have hpi4 : -(4 / 5 : ℝ) < -(Real.pi / 4) := by linarith
    have hexp_gt : Real.exp (-(4 / 5 : ℝ)) < Real.exp (-(Real.pi / 4)) := Real.exp_lt_exp.mpr hpi4
    have h5 : (2 / 5 : ℝ) ^ 5 < (Real.exp (-(4 / 5 : ℝ))) ^ 5 := by
      have h_inv : (Real.exp (-(4 / 5 : ℝ))) ^ 5 = ((Real.exp 1) ^ 4)⁻¹ := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_neg]
        congr 1; norm_num
      rw [h_inv]
      have hpos : 0 < (Real.exp 1) ^ 4 := by positivity
      rw [lt_inv_comm₀ (by norm_num : (0 : ℝ) < (2 / 5) ^ 5) hpos]
      exact lt_trans (pow_lt_pow_left₀ he_hi (Real.exp_nonneg _) (by norm_num)) (by norm_num)
    have h25 : (2 : ℝ) / 5 < Real.exp (-(4 / 5 : ℝ)) := by
      by_contra hle
      push Not at hle
      have := pow_le_pow_left₀ (Real.exp_nonneg _) hle 5
      linarith [h5]
    exact lt_trans h25 hexp_gt

private lemma elementary_ineq_large_delta {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {t : ℝ} (hlo : -(23 / 16) ≤ t) (hhi : t ≤ -1) :
    let E : ℝ := 3 / (16 * Real.pi ^ 2)
    let X : ℝ → ℝ := fun u =>
      (2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (-(σ * (Real.pi / 4) * u)) /
        Real.sqrt (Real.cosh (Real.pi * u))
    0 < X (-1) - E ∧
      Real.exp (-(σ * (Real.pi / 4) * (t + 1))) * (X t + E) ≤ (3 / 2) * (X (-1) - E) := by
  intro E X
  have hpi_lo : (3.14 : ℝ) < Real.pi := lt_trans (by norm_num) Real.pi_gt_d20
  have hpi_hi : Real.pi < (3.15 : ℝ) := lt_trans Real.pi_lt_d20 (by norm_num)
  obtain ⟨hexp2pi_lt, hexppi_gt, hexppi4_gt⟩ := exp_bounds_aux
  have hE_pos : 0 < E := by dsimp [E]; positivity
  have hE_hi : E < 3 / (16 * (3.14 : ℝ) ^ 2) := by
    dsimp [E]
    gcongr
  rcases hσ with rfl | rfl
  · -- Case σ = 1
    have hcosh_m1 : Real.cosh (Real.pi * (-1)) ≤ ((11 / 10 : ℝ) * Real.exp (Real.pi / 2) / Real.sqrt 2) ^ 2 := by
      rw [Real.cosh_eq, div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      have h1 : Real.exp (-(Real.pi * (-1))) = Real.exp Real.pi := by ring_nf
      have h2 : Real.exp (Real.pi * (-1)) = Real.exp (-Real.pi) := by ring_nf
      rw [h1, h2]
      have hexp_sq : (Real.exp (Real.pi / 2)) ^ 2 = Real.exp Real.pi := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      rw [hexp_sq]
      have hexp_neg : Real.exp (-Real.pi) ≤ (21 / 100 : ℝ) * Real.exp Real.pi := by
        have hprod : Real.exp (-Real.pi) * Real.exp Real.pi = 1 := by
          rw [← Real.exp_add]; simp
        have h400 : (400 : ℝ) < (Real.exp Real.pi) ^ 2 := by
          nlinarith [hexppi_gt]
        nlinarith [Real.exp_pos (-Real.pi), Real.exp_pos Real.pi]
      linarith
    have hsqrt_m1 : Real.sqrt (Real.cosh (Real.pi * (-1))) ≤
        (11 / 10 : ℝ) * Real.exp (Real.pi / 2) / Real.sqrt 2 := by
      exact le_trans (Real.sqrt_le_sqrt hcosh_m1)
        (Real.sqrt_sq (by positivity : 0 ≤ (11 / 10 : ℝ) * Real.exp (Real.pi / 2) / Real.sqrt 2)).le
    have hXm1_ge : (10 / 11 : ℝ) * (2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (-(Real.pi / 4)) ≤ X (-1) := by
      dsimp [X]
      have hspos : 0 < Real.sqrt (Real.cosh (Real.pi * (-1))) := Real.sqrt_pos.mpr (Real.cosh_pos _)
      have h1 : (2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (-(1 * (Real.pi / 4) * (-1))) /
          ((11 / 10 : ℝ) * Real.exp (Real.pi / 2) / Real.sqrt 2) ≤
          (2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (-(1 * (Real.pi / 4) * (-1))) /
            Real.sqrt (Real.cosh (Real.pi * (-1))) :=
        div_le_div_of_nonneg_left (by positivity) hspos hsqrt_m1
      refine le_trans ?_ h1
      have h2r : (2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.sqrt 2 = (2 : ℝ) ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by norm_num)]
        norm_num
      have hexp_div : Real.exp (-(1 * (Real.pi / 4) * (-1))) / Real.exp (Real.pi / 2) =
          Real.exp (-(Real.pi / 4)) := by
        rw [← Real.exp_sub]
        congr 1; ring
      have heq_alg : (10 / 11 : ℝ) * (2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (-(Real.pi / 4)) =
          (2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (-(1 * (Real.pi / 4) * (-1))) /
            ((11 / 10 : ℝ) * Real.exp (Real.pi / 2) / Real.sqrt 2) := by
        rw [← h2r, ← hexp_div]
        have hs2_ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
        have he2_ne : Real.exp (Real.pi / 2) ≠ 0 := (Real.exp_pos _).ne'
        field_simp [hs2_ne, he2_ne]
      exact heq_alg.le
    have h2_14_ge : (1 : ℝ) ≤ (2 : ℝ) ^ (1 / 4 : ℝ) :=
      Real.one_le_rpow (by norm_num) (by norm_num)
    have hXm1_num : (1 / 4 : ℝ) < X (-1) - E := by
      have h1 : (10 / 11 : ℝ) * 1 * (2 / 5 : ℝ) ≤ (10 / 11 : ℝ) * (2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (-(Real.pi / 4)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left h2_14_ge (by norm_num)) hexppi4_gt.le (by norm_num) (by positivity)
      linarith [hE_hi, hXm1_ge]
    refine ⟨by linarith, ?_⟩
    -- Bound LHS for σ = 1:
    have hcosh_t : (Real.exp (-((Real.pi / 2) * t)) / Real.sqrt 2) ^ 2 ≤ Real.cosh (Real.pi * t) := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), ← Real.exp_nat_mul, Real.cosh_eq]
      have : (2 : ℕ) * -((Real.pi / 2) * t) = -(Real.pi * t) := by push_cast; ring
      rw [this]
      linarith [Real.exp_pos (Real.pi * t)]
    have hsqrt_t : Real.exp (-((Real.pi / 2) * t)) / Real.sqrt 2 ≤ Real.sqrt (Real.cosh (Real.pi * t)) := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ Real.exp (-((Real.pi / 2) * t)) / Real.sqrt 2)]
      exact Real.sqrt_le_sqrt hcosh_t
    have hXt_le : Real.exp (-(1 * (Real.pi / 4) * (t + 1))) * X t ≤
        (2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (-(Real.pi / 4)) := by
      dsimp [X]
      have h1 : (2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (-(1 * (Real.pi / 4) * t)) /
          Real.sqrt (Real.cosh (Real.pi * t)) ≤
          (2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (-(1 * (Real.pi / 4) * t)) /
            (Real.exp (-((Real.pi / 2) * t)) / Real.sqrt 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hsqrt_t
      have h2 : Real.exp (-(1 * (Real.pi / 4) * (t + 1))) *
          ((2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (-(1 * (Real.pi / 4) * t)) /
            (Real.exp (-((Real.pi / 2) * t)) / Real.sqrt 2)) =
          (2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (-(Real.pi / 4)) := by
        have h2r : (2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.sqrt 2 = (2 : ℝ) ^ (1 / 4 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by norm_num)]; norm_num
        have hexp_c : Real.exp (-(1 * (Real.pi / 4) * (t + 1))) * Real.exp (-(1 * (Real.pi / 4) * t)) /
            Real.exp (-((Real.pi / 2) * t)) = Real.exp (-(Real.pi / 4)) := by
          rw [← Real.exp_add, ← Real.exp_sub]
          congr 1; ring
        calc
          Real.exp (-(1 * (Real.pi / 4) * (t + 1))) *
              ((2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (-(1 * (Real.pi / 4) * t)) /
                (Real.exp (-((Real.pi / 2) * t)) / Real.sqrt 2))
            = ((2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.sqrt 2) *
                (Real.exp (-(1 * (Real.pi / 4) * (t + 1))) * Real.exp (-(1 * (Real.pi / 4) * t)) /
                  Real.exp (-((Real.pi / 2) * t))) := by field_simp
          _ = (2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (-(Real.pi / 4)) := by rw [h2r, hexp_c]
      exact le_trans (mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg _)) h2.le
    have hexp_t1 : Real.exp (-(1 * (Real.pi / 4) * (t + 1))) ≤ 2 := by
      have ht_arg : -(1 * (Real.pi / 4) * (t + 1)) ≤ 1 / 2 := by nlinarith [hlo, hpi_hi]
      have he_hi : Real.exp 1 < 2.719 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have hexp_half : Real.exp (1 / 2) < 2 := by
        by_contra hge
        push Not at hge
        have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hge 2
        have : (Real.exp (1 / 2)) ^ 2 = Real.exp 1 := by
          rw [← Real.exp_nat_mul]; congr 1; norm_num
        linarith
      exact le_trans (Real.exp_le_exp.mpr ht_arg) hexp_half.le
    have hE_prod : Real.exp (-(1 * (Real.pi / 4) * (t + 1))) * E ≤ 2 * E :=
      mul_le_mul_of_nonneg_right hexp_t1 hE_pos.le
    -- Now check: `2^(1/4) * exp(-π/4) + 2*E ≤ (3/2) * ((10/11) * 2^(1/4) * exp(-π/4) - E)`
    -- i.e. `(7/2) * E ≤ (4/11) * 2^(1/4) * exp(-π/4)`!
    have hgap : (7 / 2 : ℝ) * E ≤ (4 / 11 : ℝ) * ((2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (-(Real.pi / 4))) := by
      have h1 : (1 : ℝ) * (2 / 5 : ℝ) ≤ (2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (-(Real.pi / 4)) :=
        mul_le_mul h2_14_ge hexppi4_gt.le (by norm_num) (by positivity)
      linarith [hE_hi]
    linarith [mul_add (Real.exp (-(1 * (Real.pi / 4) * (t + 1)))) (X t) E, hXt_le, hE_prod, hXm1_ge, hgap]
  · -- Case σ = -1
    have h5E_le : 5 * E < X (-1) := by
      dsimp [X]
      -- Raise to 4th power!
      have h_rhs_pos : 0 < (2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (-(-1 * (Real.pi / 4) * (-1))) /
          Real.sqrt (Real.cosh (Real.pi * (-1))) := by positivity
      have hpow4 : (5 * E) ^ 4 < ((2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (-(-1 * (Real.pi / 4) * (-1))) /
          Real.sqrt (Real.cosh (Real.pi * (-1)))) ^ 4 := by
        rw [div_pow, mul_pow, mul_pow]
        have h2_4 : ((2 : ℝ) ^ (-(1 / 4 : ℝ))) ^ 4 = 1 / 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          norm_num
        have hexp_4 : (Real.exp (-(-1 * (Real.pi / 4) * (-1)))) ^ 4 = Real.exp (-Real.pi) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        have hsqrt_4 : (Real.sqrt (Real.cosh (Real.pi * (-1)))) ^ 4 = (Real.cosh Real.pi) ^ 2 := by
          have hc_even : Real.cosh (Real.pi * (-1)) = Real.cosh Real.pi := by
            rw [mul_neg, mul_one, Real.cosh_neg]
          rw [hc_even, show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (Real.cosh_pos _).le]
        rw [h2_4, hexp_4, hsqrt_4]
        have hcosh_id : Real.exp (-Real.pi) / (Real.cosh Real.pi) ^ 2 =
            4 * Real.exp Real.pi / (Real.exp (2 * Real.pi) + 1) ^ 2 := by
          rw [Real.cosh_eq]
          have h1 : Real.exp Real.pi + Real.exp (-Real.pi) =
              Real.exp (-Real.pi) * (Real.exp (2 * Real.pi) + 1) := by
            rw [mul_add, ← Real.exp_add, mul_one]
            congr 2; ring
          have h2 : (Real.exp (-Real.pi)) ^ 2 * Real.exp Real.pi = Real.exp (-Real.pi) := by
            rw [← Real.exp_nat_mul, ← Real.exp_add]
            congr 1; push_cast; ring
          have h3 : Real.exp (-Real.pi) * Real.exp Real.pi = 1 := by
            rw [← Real.exp_add]; simp
          have hexp_ne : Real.exp (-Real.pi) ≠ 0 := (Real.exp_pos _).ne'
          have hden_ne : Real.exp (2 * Real.pi) + 1 ≠ 0 := by positivity
          rw [h1]
          field_simp [hexp_ne, hden_ne]
          linear_combination -4 * h3
        rw [show (1 / 2 : ℝ) * Real.exp (-Real.pi) / Real.cosh Real.pi ^ 2 =
            (1 / 2) * (Real.exp (-Real.pi) / Real.cosh Real.pi ^ 2) by ring, hcosh_id]
        have h_lhs : 5 ^ 4 * E ^ 4 < (15 / (16 * (3.14 : ℝ) ^ 2)) ^ 4 := by
          rw [← mul_pow]
          have : 5 * E < 15 / (16 * (3.14 : ℝ) ^ 2) := by linarith [hE_hi]
          exact pow_lt_pow_left₀ this (by positivity) (by norm_num)
        have h_mid : (15 / (16 * (3.14 : ℝ) ^ 2)) ^ 4 <
            (1 / 2 : ℝ) * (4 * 20 / (570 + 1) ^ 2) := by norm_num
        have h_rhs : (1 / 2 : ℝ) * (4 * 20 / (570 + 1) ^ 2) <
            (1 / 2 : ℝ) * (4 * Real.exp Real.pi / (Real.exp (2 * Real.pi) + 1) ^ 2) := by
          have hd : (Real.exp (2 * Real.pi) + 1) ^ 2 < (570 + 1 : ℝ) ^ 2 :=
            pow_lt_pow_left₀ (by linarith [hexp2pi_lt]) (by positivity) (by norm_num)
          have hn : (4 : ℝ) * 20 < 4 * Real.exp Real.pi := by linarith [hexppi_gt]
          have hf1 : (4 : ℝ) * 20 / (570 + 1) ^ 2 < 4 * 20 / (Real.exp (2 * Real.pi) + 1) ^ 2 :=
            div_lt_div_of_pos_left (by norm_num) (by positivity) hd
          have hf2 : (4 : ℝ) * 20 / (Real.exp (2 * Real.pi) + 1) ^ 2 <
              4 * Real.exp Real.pi / (Real.exp (2 * Real.pi) + 1) ^ 2 :=
            div_lt_div_of_pos_right hn (by positivity)
          linarith
        exact lt_trans h_lhs (lt_trans h_mid h_rhs)
      by_contra hge
      push Not at hge
      have := pow_le_pow_left₀ h_rhs_pos.le hge 4
      linarith
    refine ⟨by linarith, ?_⟩
    -- Monotonicity on t ≤ -1 for σ = -1:
    have hexp_pref : Real.exp (-(-1 * (Real.pi / 4) * (t + 1))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [hhi, Real.pi_pos]
    have hcosh_mono : Real.cosh (Real.pi * (-1)) ≤ Real.cosh (Real.pi * t) := by
      rw [Real.cosh_eq, Real.cosh_eq]
      have hy1 : Real.pi ≤ -(Real.pi * t) := by nlinarith [hhi, Real.pi_pos]
      have hdiff : (Real.exp (-(Real.pi * t)) + Real.exp (Real.pi * t)) -
          (Real.exp Real.pi + Real.exp (-Real.pi)) =
          (Real.exp (-(Real.pi * t)) - Real.exp Real.pi) *
            (1 - Real.exp (Real.pi * t - Real.pi)) := by
        have h1 : Real.exp (-(Real.pi * t)) * Real.exp (Real.pi * t - Real.pi) = Real.exp (-Real.pi) := by
          rw [← Real.exp_add]; congr 1; ring
        have h2 : Real.exp Real.pi * Real.exp (Real.pi * t - Real.pi) = Real.exp (Real.pi * t) := by
          rw [← Real.exp_add]; congr 1; ring
        linear_combination h1 - h2
      have hf1 : 0 ≤ Real.exp (-(Real.pi * t)) - Real.exp Real.pi :=
        sub_nonneg.mpr (Real.exp_le_exp.mpr hy1)
      have hf2 : 0 ≤ 1 - Real.exp (Real.pi * t - Real.pi) :=
        sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [hhi, Real.pi_pos]))
      have hprod_nn : 0 ≤ (Real.exp (-(Real.pi * t)) - Real.exp Real.pi) *
          (1 - Real.exp (Real.pi * t - Real.pi)) := mul_nonneg hf1 hf2
      have hneg1 : Real.exp (Real.pi * (-1)) = Real.exp (-Real.pi) := by ring_nf
      have hneg2 : Real.exp (-(Real.pi * (-1))) = Real.exp Real.pi := by ring_nf
      rw [hneg1, hneg2]
      linarith
    have hXt_le_Xm1 : X t ≤ X (-1) := by
      dsimp [X]
      have hexp_t_le : Real.exp (-(-1 * (Real.pi / 4) * t)) ≤ Real.exp (-(-1 * (Real.pi / 4) * (-1))) :=
        Real.exp_le_exp.mpr (by nlinarith [hhi, Real.pi_pos])
      have hnum_le : (2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (-(-1 * (Real.pi / 4) * t)) ≤
          (2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (-(-1 * (Real.pi / 4) * (-1))) :=
        mul_le_mul_of_nonneg_left hexp_t_le (by positivity)
      have hden_le : Real.sqrt (Real.cosh (Real.pi * (-1))) ≤ Real.sqrt (Real.cosh (Real.pi * t)) :=
        Real.sqrt_le_sqrt hcosh_mono
      exact div_le_div₀ (by positivity) hnum_le (Real.sqrt_pos.mpr (Real.cosh_pos _)) hden_le
    have hXtE_nn : 0 ≤ X t + E := by
      dsimp [X]; positivity
    calc
      Real.exp (-(-1 * (Real.pi / 4) * (t + 1))) * (X t + E)
          ≤ 1 * (X t + E) := mul_le_mul_of_nonneg_right hexp_pref hXtE_nn
      _ ≤ X (-1) + E := by linarith
      _ ≤ (3 / 2) * (X (-1) - E) := by linarith [h5E_le]

end

theorem solution (δ : ℝ) (hδ : 1 ≤ |δ|) {t : ℝ} (hlo : -(23 / 16) ≤ t) (hhi : t ≤ -1) :
    ‖mellin (fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ)))
      ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖mellin (fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ)))
        ((1 / 2 : ℂ) - Complex.I)‖ := by
  have hpos : 0 < |δ| := lt_of_lt_of_le zero_lt_one hδ
  let σ : ℝ := if 0 ≤ δ then 1 else -1
  let W : ℝ := 2 * Real.pi * |δ|
  have hσ : σ = 1 ∨ σ = -1 := by
    dsimp [σ]; split_ifs <;> [exact Or.inl rfl; exact Or.inr rfl]
  have hW_pos : 0 < W := by dsimp [W]; positivity
  have hW_ge : 2 * Real.pi ≤ W := by
    dsimp [W]
    nlinarith [Real.pi_pos, hδ]
  have hs0_eq : ((1 / 2 : ℂ) - Complex.I) = ((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  rw [hs0_eq]
  rw [norm_mellin_gauss_eq hδ t hpos, norm_mellin_gauss_eq hδ (-1) hpos]
  let s : ℂ := (1 / 2 : ℂ) + (t : ℝ) * Complex.I
  let s₀ : ℂ := (1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I
  have hs_re : s.re = 1 / 2 := by simp [s]
  have hs0_re : s₀.re = 1 / 2 := by simp [s₀]
  have herr_t := norm_J_sub_J_inf_le hσ hW_ge hs_re
  have herr_0 := norm_J_sub_J_inf_le hσ hW_ge hs0_re
  have hJt_le : ‖J_int σ W s‖ ≤ ‖J_inf σ s‖ + 3 * Real.sqrt Real.pi / (16 * Real.pi ^ 2) := by
    have := norm_sub_norm_le (J_int σ W s) (J_inf σ s)
    linarith
  have hJ0_ge : ‖J_inf σ s₀‖ - 3 * Real.sqrt Real.pi / (16 * Real.pi ^ 2) ≤ ‖J_int σ W s₀‖ := by
    have := norm_sub_norm_le (J_inf σ s₀) (J_int σ W s₀)
    rw [norm_sub_rev] at this
    linarith
  obtain ⟨hden_pos, hineq⟩ := elementary_ineq_large_delta hσ hlo hhi
  let E : ℝ := 3 / (16 * Real.pi ^ 2)
  let X : ℝ → ℝ := fun u =>
    (2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (-(σ * (Real.pi / 4) * u)) /
      Real.sqrt (Real.cosh (Real.pi * u))
  have hJinf_t : ‖J_inf σ s‖ = Real.sqrt Real.pi * X t := norm_J_inf_eq hσ t
  have hJinf_0 : ‖J_inf σ s₀‖ = Real.sqrt Real.pi * X (-1) := norm_J_inf_eq hσ (-1)
  have hE_eq : 3 * Real.sqrt Real.pi / (16 * Real.pi ^ 2) = Real.sqrt Real.pi * E := by
    dsimp [E]; ring
  rw [hJinf_t, hE_eq] at hJt_le
  rw [hJinf_0, hE_eq] at hJ0_ge
  have hw_t := norm_rayWeight_one_cpow t hσ
  have hw_0 := norm_rayWeight_one_cpow (-1) hσ
  have hw_ratio : ‖rayWeight σ 1 ^ s‖ =
      ‖rayWeight σ 1 ^ s₀‖ * Real.exp (-(σ * (Real.pi / 4) * (t + 1))) := by
    dsimp only [s, s₀]
    rw [hw_t, hw_0, mul_assoc ((2 : ℝ) ^ (1 / 4 : ℝ)), ← Real.exp_add]
    congr 2; ring
  have hc_pos : 0 < W ^ (-(1 / 2 : ℝ)) * ‖rayWeight σ 1 ^ s₀‖ * Real.sqrt Real.pi := by
    have hw0_pos : 0 < ‖rayWeight σ 1 ^ s₀‖ := by
      dsimp only [s₀]; rw [hw_0]; positivity
    have hpi_sqrt_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    positivity
  calc
    W ^ (-(1 / 2 : ℝ)) * ‖rayWeight σ 1 ^ s‖ * ‖J_int σ W s‖
      ≤ W ^ (-(1 / 2 : ℝ)) * ‖rayWeight σ 1 ^ s‖ * (Real.sqrt Real.pi * X t + Real.sqrt Real.pi * E) :=
        mul_le_mul_of_nonneg_left hJt_le (by positivity)
    _ = (W ^ (-(1 / 2 : ℝ)) * ‖rayWeight σ 1 ^ s₀‖ * Real.sqrt Real.pi) *
          (Real.exp (-(σ * (Real.pi / 4) * (t + 1))) * (X t + E)) := by
        rw [hw_ratio]; ring
    _ ≤ (W ^ (-(1 / 2 : ℝ)) * ‖rayWeight σ 1 ^ s₀‖ * Real.sqrt Real.pi) *
          ((3 / 2) * (X (-1) - E)) :=
        mul_le_mul_of_nonneg_left hineq hc_pos.le
    _ = (3 / 2) * (W ^ (-(1 / 2 : ℝ)) * ‖rayWeight σ 1 ^ s₀‖ *
          (Real.sqrt Real.pi * X (-1) - Real.sqrt Real.pi * E)) := by ring
    _ ≤ (3 / 2) * (W ^ (-(1 / 2 : ℝ)) * ‖rayWeight σ 1 ^ s₀‖ * ‖J_int σ W s₀‖) := by
        gcongr
