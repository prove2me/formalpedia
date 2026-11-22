-- Prove2me | solution 1 for Formalism.mellinDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:03:17.95778+00:00
-- url     : https://prove2.me/submissions/dde284ad-3c81-4aab-9774-619463f34c7c

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_MellinDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
namespace Formalism
theorem _root_.solution : MellinDeriv := by
  intro H σs hH hint s hs
  set μ : Measure ℝ := volume.restrict (Ioi (1:ℝ)) with hμ
  set η : ℝ := (s.re - σs) / 3 with hη
  have hηpos : 0 < η := by rw [hη]; linarith

  have hcpow_meas : ∀ c : ℂ, Measurable (fun x : ℝ => (x : ℂ) ^ c) :=
    fun c => (Complex.measurable_ofReal).pow_const c
  have hF_meas : ∀ z : ℂ, AEStronglyMeasurable (fun x : ℝ => H x * (x : ℂ) ^ (-z - 1)) μ :=
    fun z => hH.mul (hcpow_meas _).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable
      (fun x : ℝ => -(Real.log x : ℂ) * H x * (x : ℂ) ^ (-s - 1)) μ := by
    have hlog : Measurable (fun x : ℝ => -(Real.log x : ℂ)) :=
      (Complex.measurable_ofReal.comp Real.measurable_log).neg
    exact (hlog.aestronglyMeasurable.mul hH).mul (hcpow_meas _).aestronglyMeasurable

  have hF_int : Integrable (fun x : ℝ => H x * (x : ℂ) ^ (-s - 1)) μ := by
    have h1 := hint s.re hs
    refine Integrable.mono' h1 (hF_meas s) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro x hx
    have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    simp

  set bound : ℝ → ℝ := fun x => ‖H x‖ * x ^ (-(s.re - 2 * η) - 1) / η with hbound
  have hbound_int : Integrable bound μ := by
    have h1 := hint (s.re - 2 * η) (by rw [hη]; linarith)
    exact h1.div_const η
  have h_bound : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s η,
      ‖-(Real.log x : ℂ) * H x * (x : ℂ) ^ (-z - 1)‖ ≤ bound x := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro x hx z hz
    have hx1 : (1:ℝ) < x := hx
    have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx
    have hzre : s.re - η < z.re := by
      have : |z.re - s.re| < η := by
        have h := Metric.mem_ball.1 hz
        rw [Complex.dist_eq] at h
        calc |z.re - s.re| = |(z - s).re| := by simp
          _ ≤ ‖z - s‖ := Complex.abs_re_le_norm _
          _ < η := h
      have := (abs_lt.1 this).1
      linarith
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1.le
    have hlogle : Real.log x ≤ x ^ η / η := Real.log_le_rpow_div hx0.le hηpos
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real,
      Real.norm_of_nonneg hlog0]
    have hre : (-z - 1).re = -z.re - 1 := by simp
    rw [hre]
    have hpow : x ^ (-z.re - 1) ≤ x ^ (-(s.re - η) - 1) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    have hHn : 0 ≤ ‖H x‖ := norm_nonneg _
    have hp0 : 0 ≤ x ^ (-z.re - 1) := Real.rpow_nonneg hx0.le _
    have hmul : x ^ η * x ^ (-(s.re - η) - 1) = x ^ (-(s.re - 2 * η) - 1) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    calc Real.log x * ‖H x‖ * x ^ (-z.re - 1)
        ≤ (x ^ η / η) * ‖H x‖ * x ^ (-(s.re - η) - 1) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hlogle hHn) hpow hp0
          exact mul_nonneg (div_nonneg (Real.rpow_nonneg hx0.le _) hηpos.le) hHn
      _ = bound x := by
          rw [hbound]; simp only
          rw [← hmul]; field_simp
  have h_diff : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s η,
      HasDerivAt (fun w : ℂ => H x * (x : ℂ) ^ (-w - 1))
        (-(Real.log x : ℂ) * H x * (x : ℂ) ^ (-z - 1)) z := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro x hx z _
    have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx
    have hf : HasDerivAt (fun w : ℂ => -w - 1) (-1) z := by
      simpa using ((hasDerivAt_id z).neg.sub_const (1:ℂ))
    have hc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    have h2 := (hf.const_cpow (c := (x:ℂ)) (Or.inl hc)).const_mul (H x)
    refine h2.congr_deriv ?_
    rw [← Complex.ofReal_log hx0.le]
    ring
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun z x => H x * (x : ℂ) ^ (-z - 1))
    (F' := fun z x => -(Real.log x : ℂ) * H x * (x : ℂ) ^ (-z - 1))
    (Metric.ball_mem_nhds s hηpos) (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas
    h_bound hbound_int h_diff
  exact this.2
end Formalism
