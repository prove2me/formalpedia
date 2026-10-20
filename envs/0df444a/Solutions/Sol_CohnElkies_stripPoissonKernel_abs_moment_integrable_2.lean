-- Prove2me | solution 2 for CohnElkies.stripPoissonKernel_abs_moment_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:28:09.393829+00:00
-- url     : https://prove2.me/submissions/64495bb6-d4e1-4298-a161-423c3d5bfd8c

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
theorem h47_int_abs_pow_exp (n : ℕ) {a : ℝ} (ha : 0 < a) :
    MeasureTheory.Integrable (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) := by
  have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := a)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos ha
  have hIoi : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Ioi 0) := by
    refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0:ℝ) < x := hx
    simp [abs_of_pos hx0, Real.rpow_natCast]
  have hIio : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Iio 0) := by
    have := (show MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Ioi (-0)) by
      simpa using hIoi).comp_neg_Iio
    simpa [abs_neg] using this
  have hall : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Iic 0 ∪ Set.Ioi 0) :=
    ((integrableOn_Iic_iff_integrableOn_Iio (b := (0:ℝ))).mpr hIio).union hIoi
  rw [Set.Iic_union_Ioi, MeasureTheory.integrableOn_univ] at hall
  exact hall

theorem h47_strip_le {σ : ℝ} (hzero : 0 ≤ σ) (habove : σ < 1) (T : ℝ) :
    CohnElkies.stripPoissonKernel σ T ≤ CohnElkies.stripBottomMass σ * CohnElkies.stripPoissonExponentialMajorant T := by
  unfold CohnElkies.stripPoissonKernel CohnElkies.stripBottomMass CohnElkies.stripPoissonExponentialMajorant CohnElkies.stripAngle
  have hpi := Real.pi_pos
  have hc : Real.cos (Real.pi * (1 + σ) / 2) ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le (by nlinarith) (by nlinarith)
  have hs : 0 ≤ Real.sin (Real.pi * (1 + σ) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith)
  have hsθ : Real.sin (Real.pi * (1 + σ) / 2) ≤ Real.pi * (1 - σ) / 2 := by
    have : Real.sin (Real.pi * (1 + σ) / 2) = Real.sin (Real.pi * (1 - σ) / 2) := by
      rw [← Real.sin_pi_sub]; congr 1; ring
    rw [this]; exact Real.sin_le (by nlinarith)
  have hch : Real.exp (Real.pi / 2 * |T|) / 2 ≤ Real.cosh (Real.pi * T / 2) := by
    rw [← Real.cosh_abs, Real.cosh_eq]
    have : |Real.pi * T / 2| = Real.pi / 2 * |T| := by
      rw [abs_div, abs_mul, abs_of_pos hpi]; norm_num; ring
    rw [this]
    linarith [Real.exp_pos (-(Real.pi / 2 * |T|))]
  have hG := Real.exp_pos (Real.pi / 2 * |T|)
  have hFG : Real.exp (-(Real.pi / 2) * |T|) * Real.exp (Real.pi / 2 * |T|) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have hD : 0 < 4 * (Real.cosh (Real.pi * T / 2) - Real.cos (Real.pi * (1 + σ) / 2)) := by
    nlinarith
  rw [div_le_iff₀ hD]
  have hF := Real.exp_pos (-(Real.pi / 2) * |T|)
  have h1σ : 0 ≤ 1 - σ := by linarith
  have key : (1 - σ) / 2 * (Real.pi / 2 * Real.exp (-(Real.pi / 2) * |T|)) *
      (4 * (Real.exp (Real.pi / 2 * |T|) / 2)) = Real.pi * (1 - σ) / 2 := by
    have : (1 - σ) / 2 * (Real.pi / 2 * Real.exp (-(Real.pi / 2) * |T|)) *
      (4 * (Real.exp (Real.pi / 2 * |T|) / 2)) =
        (1 - σ) / 2 * (Real.pi / 2) * 2 * (Real.exp (-(Real.pi / 2) * |T|) * Real.exp (Real.pi / 2 * |T|)) := by ring
    rw [this, hFG]; ring
  have hR : 0 ≤ (1 - σ) / 2 * (Real.pi / 2 * Real.exp (-(Real.pi / 2) * |T|)) := by positivity
  have hmono : 4 * (Real.exp (Real.pi / 2 * |T|) / 2) ≤
      4 * (Real.cosh (Real.pi * T / 2) - Real.cos (Real.pi * (1 + σ) / 2)) := by linarith
  calc Real.sin (Real.pi * (1 + σ) / 2) ≤ Real.pi * (1 - σ) / 2 := hsθ
    _ = _ := key.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono hR

theorem solution
    {σ : ℝ} (hzero : 0 ≤ σ) (habove : σ < 1) :
    Integrable (fun T : ℝ => stripPoissonKernel σ T * |T|) := by
  have hmaj := (h47_int_abs_pow_exp 1 (by positivity : (0:ℝ) < Real.pi / 2)).const_mul
    (stripBottomMass σ * (Real.pi / 2))
  have hmeas : Measurable (fun T : ℝ => stripPoissonKernel σ T * |T|) := by
    unfold stripPoissonKernel; fun_prop
  refine hmaj.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun T => ?_)
  have hpi := Real.pi_pos
  have hK0 : 0 ≤ stripPoissonKernel σ T := by
    unfold stripPoissonKernel stripAngle
    have hc : Real.cos (Real.pi * (1 + σ) / 2) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le (by nlinarith) (by nlinarith)
    have hs : 0 ≤ Real.sin (Real.pi * (1 + σ) / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith)
    have := Real.one_le_cosh (Real.pi * T / 2)
    apply div_nonneg hs; nlinarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK0, abs_abs]
  have hle := h47_strip_le hzero habove T
  unfold stripPoissonExponentialMajorant at hle
  calc stripPoissonKernel σ T * |T| ≤ stripBottomMass σ * (Real.pi / 2 * Real.exp (-(Real.pi / 2) * |T|)) * |T| :=
        mul_le_mul_of_nonneg_right hle (abs_nonneg T)
    _ = stripBottomMass σ * (Real.pi / 2) * (|T| ^ 1 * Real.exp (-(Real.pi / 2) * |T|)) := by ring

