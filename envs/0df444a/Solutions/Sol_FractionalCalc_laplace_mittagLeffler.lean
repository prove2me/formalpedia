-- Prove2me | solution 1 for FractionalCalc.laplace_mittagLeffler
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T07:51:52.261284+00:00
-- url     : https://prove2.me/submissions/0c845b3f-72f4-465d-93ff-85939103d7a3

import Mathlib
import Definitions.Def_FractionalCalc_mittagLeffler
import Definitions.Def_QueueingFundamentals_Transient_laplace
set_option autoImplicit false
open MeasureTheory Set Classical QueueingFundamentals.Transient

namespace FractionalCalc

private lemma fc1_norm_term {s : ℂ} {a t : ℝ} (ht : 0 < t) :
    ‖Complex.exp (-s * (t : ℂ)) * ((t ^ (a - 1) : ℝ) : ℂ)‖ = t ^ (a - 1) * Real.exp (-s.re * t) := by
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg ht.le _)]
  simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  ring

private lemma fc1_meas (s : ℂ) (a : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * ((t ^ (a - 1) : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) := by
  apply Measurable.aestronglyMeasurable
  fun_prop

private lemma fc1_int {s : ℂ} {a : ℝ} (ha : 0 < a) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * ((t ^ (a - 1) : ℝ) : ℂ)) (Ioi 0) := by
  have hb : IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-s.re * t ^ (1:ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos hs
  refine Integrable.mono' hb (fc1_meas s a) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
  rw [fc1_norm_term ht, Real.rpow_one]

private lemma fc1_real_case {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫ t in Ioi (0:ℝ), Complex.exp (-(r : ℂ) * (t : ℂ)) * ((t ^ (a - 1) : ℝ) : ℂ) =
      (1 / (r : ℂ)) ^ (a : ℂ) * Complex.Gamma a := by
  have h1 : ∀ t : ℝ, Complex.exp (-(r : ℂ) * (t : ℂ)) * ((t ^ (a - 1) : ℝ) : ℂ) =
      ((t ^ (a - 1) * Real.exp (-(r * t)) : ℝ) : ℂ) := by
    intro t; push_cast; ring_nf
  simp_rw [h1]
  rw [integral_complex_ofReal, Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr, Complex.ofReal_mul,
    Complex.ofReal_cpow (by positivity), Complex.Gamma_ofReal]
  push_cast; rfl

private lemma fc1_diff {a : ℝ} (ha : 0 < a) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ t in Ioi (0:ℝ), Complex.exp (-s * (t : ℂ)) * ((t ^ (a - 1) : ℝ) : ℂ))
      {s | 0 < s.re} := by
  intro s₀ hs₀
  simp only [mem_ofPred_eq] at hs₀
  refine DifferentiableAt.differentiableWithinAt ?_
  set ε := s₀.re / 2 with hε
  have hεpos : 0 < ε := by positivity
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun s t => Complex.exp (-s * (t : ℂ)) * ((t ^ (a - 1) : ℝ) : ℂ))
    (F' := fun s t => -(t : ℂ) * Complex.exp (-s * (t : ℂ)) * ((t ^ (a - 1) : ℝ) : ℂ))
    (bound := fun t => t ^ ((a + 1) - 1) * Real.exp (-ε * t ^ (1:ℝ)))
    (x₀ := s₀) (s := Metric.ball s₀ ε) (Metric.ball_mem_nhds _ hεpos)
    (Filter.Eventually.of_forall fun s => fc1_meas s a) (fc1_int ha hs₀)
    (by apply Measurable.aestronglyMeasurable; fun_prop) ?_
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos hεpos) ?_
  · exact key.2.differentiableAt
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    intro s hs
    have ht' : (0:ℝ) < t := ht
    have hre : ε < s.re := by
      have h1 := Complex.abs_re_le_norm (s - s₀)
      rw [Metric.mem_ball, dist_eq_norm] at hs
      rw [Complex.sub_re] at h1
      have := abs_lt.mp (lt_of_le_of_lt h1 hs)
      linarith [this.1]
    rw [mul_assoc, norm_mul, fc1_norm_term ht', norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht', Real.rpow_one, add_sub_cancel_right]
    calc t * (t ^ (a - 1) * Real.exp (-s.re * t)) = t ^ a * Real.exp (-s.re * t) := by
          rw [← mul_assoc, ← Real.rpow_one_add' ht'.le (by linarith)]; ring_nf
      _ ≤ t ^ a * Real.exp (-ε * t) := by
          gcongr
  · refine Filter.Eventually.of_forall fun t s _ => ?_
    have h0 : HasDerivAt (fun y : ℂ => -y * (t : ℂ)) (-(t : ℂ)) s := by
      simpa using ((hasDerivAt_id s).neg.mul_const (t : ℂ))
    have := h0.cexp.mul_const ((t ^ (a - 1) : ℝ) : ℂ)
    exact this.congr_deriv (by ring)

private lemma fc1_cgamma {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    ∫ t in Ioi (0:ℝ), Complex.exp (-s * (t : ℂ)) * ((t ^ (a - 1) : ℝ) : ℂ) =
      (1 / s) ^ (a : ℂ) * Complex.Gamma a := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hG : DifferentiableOn ℂ (fun s : ℂ => (1 / s) ^ (a : ℂ) * Complex.Gamma a) {s | 0 < s.re} := by
    intro z hz
    simp only [mem_ofPred_eq] at hz
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.mul_const ?_ _
    refine DifferentiableAt.cpow ?_ (differentiableAt_const _) ?_
    · exact (differentiableAt_const _).div differentiableAt_id hz0
    · left
      rw [one_div, Complex.inv_re]
      exact div_pos hz (Complex.normSq_pos.mpr hz0)
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq ((fc1_diff ha).analyticOnNhd hU)
    (hG.analyticOnNhd hU) (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 1) (by simp) ?_
  · exact heq hs
  · have ht : Filter.Tendsto (fun n : ℕ => (((1:ℝ) + 1 / ((n:ℝ) + 1) : ℝ) : ℂ)) Filter.atTop
        (nhdsWithin 1 {1}ᶜ) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have := ((tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1:ℝ))
        rw [add_zero] at this
        have h3 := (Complex.continuous_ofReal.tendsto 1).comp this
        rw [Complex.ofReal_one] at h3
        exact h3
      · refine Filter.Eventually.of_forall fun n => ?_
        simp only [mem_compl_iff, mem_singleton_iff]
        intro h
        have h2 := congrArg Complex.re h
        simp only [Complex.ofReal_re, Complex.one_re] at h2
        have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
        linarith
    refine ht.frequently (Filter.Frequently.of_forall fun n => ?_)
    have hr : (0:ℝ) < 1 + 1 / ((n:ℝ) + 1) := by positivity
    exact fc1_real_case ha hr

end FractionalCalc

open FractionalCalc in
theorem solution (α β c : ℝ) (s : ℂ)
    (hα : 0 < α) (hβ : 0 < β) (hs : |c| ^ (1 / α) < s.re) :
    laplace (fun t => t ^ (β - 1) * mittagLeffler α β (-c * t ^ α)) s =
      s ^ (α - β : ℂ) / (s ^ (α : ℂ) + c) := by
  set r := s.re with hrdef
  have hr : 0 < r := lt_of_le_of_lt (Real.rpow_nonneg (abs_nonneg c) _) hs
  have hcr : |c| < r ^ α := by
    have h1 : |c| = (|c| ^ (1 / α)) ^ α := by
      rw [one_div, Real.rpow_inv_rpow (abs_nonneg c) hα.ne']
    rw [h1]
    exact Real.rpow_lt_rpow (Real.rpow_nonneg (abs_nonneg c) _) hs hα
  have hs0 : s ≠ 0 := by rintro rfl; simp [hrdef] at hr
  have hak : ∀ k : ℕ, 0 < α * k + β := fun k => by
    have := mul_nonneg hα.le (Nat.cast_nonneg (α := ℝ) k); linarith
  set term : ℕ → ℝ → ℂ := fun k t => (((-c) ^ k / Real.Gamma (α * k + β) : ℝ) : ℂ) *
    (Complex.exp (-s * (t : ℂ)) * ((t ^ (α * k + β - 1) : ℝ) : ℂ)) with hterm
  -- step 1 : expand the integrand
  have step1 : laplace (fun t => t ^ (β - 1) * mittagLeffler α β (-c * t ^ α)) s =
      ∫ t in Ioi (0:ℝ), ∑' k, term k t := by
    unfold laplace
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0:ℝ) < t := ht
    simp only [mittagLeffler, hterm]
    rw [← tsum_mul_left, Complex.ofReal_tsum, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    have hreal : t ^ (β - 1) * ((-c * t ^ α) ^ k / Real.Gamma (α * k + β)) =
        (-c) ^ k / Real.Gamma (α * k + β) * t ^ (α * k + β - 1) := by
      rw [mul_pow, ← Real.rpow_natCast (t ^ α) k, ← Real.rpow_mul ht'.le]
      have : t ^ (α * k + β - 1) = t ^ (α * k) * t ^ (β - 1) := by
        rw [← Real.rpow_add ht']; ring_nf
      rw [this]; ring
    rw [hreal]; push_cast; ring
  have hs' : 0 < s.re := hr
  have hint : ∀ k : ℕ, Integrable (term k) (volume.restrict (Ioi 0)) := fun k =>
    (fc1_int (hak k) hs').const_mul _
  have hnorm : ∀ k : ℕ, ∫ t in Ioi (0:ℝ), ‖term k t‖ = |c| ^ k * (1 / r) ^ (α * k + β) := by
    intro k
    have hG := Real.Gamma_pos_of_pos (hak k)
    simp only [hterm, norm_mul]
    rw [integral_const_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t => t ^ (α * k + β - 1) *
      Real.exp (-(r * t))) (fun t ht => by
        simp only; rw [← norm_mul, fc1_norm_term (ht : (0:ℝ) < t), neg_mul])]
    rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (hak k) hr, Complex.norm_real, Real.norm_eq_abs,
      abs_div, abs_pow, abs_neg, abs_of_pos hG]
    field_simp
  have hq : |c| * (1 / r) ^ α < 1 := by
    rw [one_div, Real.inv_rpow hr.le, ← div_eq_mul_inv, div_lt_one (by positivity)]
    exact hcr
  have hsum : Summable fun k : ℕ => ∫ t in Ioi (0:ℝ), ‖term k t‖ := by
    simp_rw [hnorm]
    refine ((summable_geometric_of_lt_one (by positivity) hq).mul_left ((1 / r) ^ β)).congr
      fun k => ?_
    rw [Real.rpow_add (by positivity), Real.rpow_mul (by positivity), Real.rpow_natCast]
    ring
  have step2 : ∫ t in Ioi (0:ℝ), ∑' k, term k t = ∑' k, ∫ t in Ioi (0:ℝ), term k t :=
    (integral_tsum_of_summable_integral_norm hint hsum).symm
  have step3 : ∀ k : ℕ, ∫ t in Ioi (0:ℝ), term k t =
      (-(c : ℂ)) ^ k * (1 / s) ^ (((α * k + β : ℝ)) : ℂ) := by
    intro k
    have hG := Real.Gamma_pos_of_pos (hak k)
    simp only [hterm]
    rw [integral_const_mul, fc1_cgamma (hak k) hs', Complex.Gamma_ofReal]
    have : ((Real.Gamma (α * k + β) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hG.ne'
    push_cast
    field_simp
  have hξ : ‖-(c : ℂ) * (1 / s) ^ (α : ℂ)‖ < 1 := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_real, norm_div,
      norm_one]
    refine lt_of_le_of_lt ?_ hq
    gcongr
    exact Complex.re_le_norm s
  have step4 : HasSum (fun k : ℕ => (-(c : ℂ)) ^ k * (1 / s) ^ (((α * k + β : ℝ)) : ℂ))
      ((1 / s) ^ (β : ℂ) * (1 - (-(c : ℂ) * (1 / s) ^ (α : ℂ)))⁻¹) := by
    have h1s : (1 / s) ≠ 0 := one_div_ne_zero hs0
    refine ((hasSum_geometric_of_norm_lt_one hξ).mul_left ((1 / s) ^ (β : ℂ))).congr_fun ?_
    intro k
    push_cast
    rw [Complex.cpow_add _ _ h1s, mul_comm (α : ℂ) (k : ℂ), Complex.cpow_nat_mul, mul_pow]
    ring
  rw [step1, step2, tsum_congr step3, step4.tsum_eq]
  -- step 5 : algebra
  have harg : s.arg ≠ Real.pi := by
    rw [Ne, Complex.arg_eq_pi_iff]; intro h; linarith [h.1]
  rw [one_div, Complex.inv_cpow _ _ harg, Complex.inv_cpow _ _ harg, Complex.cpow_sub _ _ hs0]
  have hA : s ^ (α : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hs0)
  have hB : s ^ (β : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hs0)
  have hAc : s ^ (α : ℂ) + c ≠ 0 := by
    intro h
    have h2 : ‖s ^ (α : ℂ)‖ = |c| := by
      rw [eq_neg_of_add_eq_zero_left h, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    rw [Complex.norm_cpow_real] at h2
    have : r ^ α ≤ ‖s‖ ^ α := Real.rpow_le_rpow hr.le (Complex.re_le_norm s) hα.le
    linarith
  have : 1 - -(c : ℂ) * (s ^ (α : ℂ))⁻¹ = (s ^ (α : ℂ) + c) / s ^ (α : ℂ) := by
    field_simp; ring
  rw [this]
  field_simp
