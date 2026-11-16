-- Prove2me | solution 1 for Complex.JensenFatou.lintegral_circle_limit_neglog_le
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-16T00:29:24.365273+00:00
-- url     : https://prove2.me/submissions/fb21ff12-147c-4f76-bdef-fad20a0c81fb

import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
noncomputable section
open Set Filter Metric MeasureTheory Real MeromorphicOn
open scoped Topology ENNReal NNReal
set_option autoImplicit false
namespace JensenFatouSupport

/-- Nonnegative extended negative logarithm, with the essential value `+∞` at zero. -/
def negLog (z : ℂ) : ℝ≥0∞ := (- ENNReal.log (ENNReal.ofReal ‖z‖)).toENNReal

lemma negLog_zero : negLog 0 = ⊤ := by simp [negLog]

lemma negLog_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    negLog z = ENNReal.ofReal (-Real.log ‖z‖) := by
  rw [negLog,ENNReal.log_ofReal_of_pos (norm_pos_iff.mpr hz),← EReal.coe_neg,
    EReal.real_coe_toENNReal]

lemma continuous_negLog : Continuous negLog := by
  exact EReal.continuous_toENNReal.comp
    (ENNReal.continuous_log.comp (ENNReal.continuous_ofReal.comp continuous_norm)).neg

/-- The submean inequality for the real logarithm of a nonzero analytic germ. -/
lemma log_norm_center_le_circleAverage {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0) :
    Real.log ‖f c‖ ≤ circleAverage (fun z => Real.log ‖f z‖) c R := by
  have hj := AnalyticOnNhd.circleAverage_log_norm hR.ne'
    (show AnalyticOnNhd ℂ f (closedBall c |R|) by simpa [abs_of_pos hR] using hf) hc
  rw [abs_of_pos hR] at hj
  rw [hj]
  exact le_add_of_nonneg_left (finsum_nonneg fun u => by
    by_cases hu : u ∈ closedBall c R
    · by_cases huc : u = c
      · subst u
        simp [hf.divisor_apply, hc]
      · apply mul_nonneg (by exact_mod_cast hf.divisor_nonneg u)
        apply Real.log_nonneg
        have hd : 0 < ‖c-u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huc))
        rw [le_mul_inv_iff₀ hd,one_mul]
        simpa only [mem_closedBall,dist_eq_norm'] using hu
    · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem, hu,
        show u ∉ closedBall c |R| by simpa [abs_of_pos hR] using hu])

lemma ae_ne_zero_circle {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0) :
    ∀ᵐ t ∂volume.restrict (Ioc 0 (2*Real.pi)), f (circleMap c R t) ≠ 0 := by
  have hcirc : ∀ᶠ z in codiscreteWithin (sphere c |R|), f z ≠ 0 := by
    rw [abs_of_pos hR]
    exact codiscreteWithin_mono sphere_subset_closedBall
      (hf.preimage_zero_mem_codiscreteWithin hc (mem_closedBall_self hR.le)
        ((convex_closedBall c R).isConnected ⟨c,mem_closedBall_self hR.le⟩))
  have hpre : ∀ᶠ t in codiscrete ℝ, f (circleMap c R t) ≠ 0 :=
    circleMap_preimage_codiscrete hR.ne' hcirc
  exact ae_restrict_le_codiscreteWithin measurableSet_Ioc
    (codiscreteWithin_mono (subset_univ _) hpre)

/-- The finite-radius negative-log estimate which will pass to the boundary by Fatou. -/
lemma lintegral_negLog_circle_le {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0)
    (hb : ∀ z ∈ sphere c R, ‖f z‖ ≤ 1) :
    (∫⁻ t in Ioc 0 (2*Real.pi), negLog (f (circleMap c R t))) ≤
      ENNReal.ofReal ((2*Real.pi)*(-Real.log ‖f c‖)) := by
  have ha := ae_ne_zero_circle hR hf hc
  have hlog : CircleIntegrable (fun z => Real.log ‖f z‖) c R :=
    (hf.mono (by rw [abs_of_pos hR]; exact sphere_subset_closedBall)).meromorphicOn.circleIntegrable_log_norm
  have hint : Integrable (fun t => -Real.log ‖f (circleMap c R t)‖)
      (volume.restrict (Ioc 0 (2*Real.pi))) := hlog.1.neg
  have hnonneg : ∀ t, 0 ≤ -Real.log ‖f (circleMap c R t)‖ := by
    intro t
    exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) (hb _ (circleMap_mem_sphere _ hR.le _)))
  calc
    _ = ∫⁻ t in Ioc 0 (2*Real.pi), ENNReal.ofReal (-Real.log ‖f (circleMap c R t)‖) :=
      lintegral_congr_ae (ha.mono fun t ht => negLog_of_ne_zero ht)
    _ = ENNReal.ofReal (∫ t in Ioc 0 (2*Real.pi), -Real.log ‖f (circleMap c R t)‖) :=
      (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnonneg)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hmean := log_norm_center_le_circleAverage hR hf hc
      rw [circleAverage,smul_eq_mul,intervalIntegral.integral_of_le (by positivity)] at hmean
      rw [integral_neg]
      have hpi : 0 < 2*Real.pi := by positivity
      have hh := (le_inv_mul_iff₀ hpi).mp hmean
      nlinarith

/-- Fatou transfers the disk submean bound to arbitrary almost-everywhere radial limits. -/
lemma lintegral_negLog_boundary_le {f : ℂ → ℂ} {g : ℝ → ℂ} {r : ℕ → ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hc : f 0 ≠ 0)
    (hr : ∀ n, 0 < r n ∧ r n < 1)
    (hb : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ 1)
    (hlim : ∀ᵐ t ∂volume.restrict (Ioc 0 (2*Real.pi)),
      Tendsto (fun n => f (circleMap 0 (r n) t)) atTop (𝓝 (g t))) :
    (∫⁻ t in Ioc 0 (2*Real.pi), negLog (g t)) ≤
      ENNReal.ofReal ((2*Real.pi)*(-Real.log ‖f 0‖)) := by
  have hn (n : ℕ) : AnalyticOnNhd ℂ f (closedBall 0 (r n)) :=
    (hf.analyticOnNhd isOpen_ball).mono (closedBall_subset_ball (hr n).2)
  have hmeas (n : ℕ) : Measurable (fun t => negLog (f (circleMap 0 (r n) t))) := by
    apply Continuous.measurable
    apply continuous_negLog.comp
    exact hf.continuousOn.comp_continuous (continuous_circleMap _ _) (fun t => by
      simpa [mem_ball,dist_eq_norm,abs_of_pos (hr n).1] using (hr n).2)
  have hbounds (n : ℕ) :
      (∫⁻ t in Ioc 0 (2*Real.pi), negLog (f (circleMap 0 (r n) t))) ≤
        ENNReal.ofReal ((2*Real.pi)*(-Real.log ‖f 0‖)) := by
    apply lintegral_negLog_circle_le (hr n).1 (hn n) hc
    intro z hz
    apply hb z
    exact (closedBall_subset_ball (hr n).2) (sphere_subset_closedBall hz)
  calc
    _ = ∫⁻ t in Ioc 0 (2*Real.pi), liminf (fun n => negLog (f (circleMap 0 (r n) t))) atTop := by
      apply lintegral_congr_ae
      filter_upwards [hlim] with t ht
      exact (continuous_negLog.continuousAt.tendsto.comp ht).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ t in Ioc 0 (2*Real.pi), negLog (f (circleMap 0 (r n) t))) atTop :=
      lintegral_liminf_le hmeas
    _ ≤ _ := liminf_le_of_frequently_le (Eventually.of_forall hbounds).frequently

end JensenFatouSupport

set_option autoImplicit false


theorem solution {f : ℂ → ℂ} {g : ℝ → ℂ} {r : ℕ → ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) (hc : f 0 ≠ 0)
    (hr : ∀ n, 0 < r n ∧ r n < 1)
    (hb : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ 1)
    (hlim : ∀ᵐ t ∂volume.restrict (Set.Ioc 0 (2*Real.pi)),
      Tendsto (fun n => f (circleMap 0 (r n) t)) atTop (𝓝 (g t))) :
    (∫⁻ t in Set.Ioc 0 (2*Real.pi), (-ENNReal.log (ENNReal.ofReal ‖g t‖)).toENNReal) ≤
      ENNReal.ofReal ((2*Real.pi)*(-Real.log ‖f 0‖)) := by
  exact JensenFatouSupport.lintegral_negLog_boundary_le hf hc hr hb hlim