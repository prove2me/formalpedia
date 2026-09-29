-- Prove2me | solution 1 for EulerMascheroni.Mixed.hardy_identity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T13:17:17.222473+00:00
-- url     : https://prove2.me/submissions/f2cd1ac7-84ff-4c87-b0d8-d1dfb49b9567

import Definitions.Def_eulerMascheroni_mixedCover

set_option autoImplicit false

open Filter MeasureTheory Set Real
open scoped Topology

namespace HardyFormalization

lemma gamma_log_integral_complex :
    (∫ t : ℝ in Ioi 0, ((Real.log t * Real.exp (-t) : ℝ) : ℂ)) =
      -(Real.eulerMascheroniConstant : ℂ) := by
  have hd := Complex.hasDerivAt_GammaIntegral (s := 1) (by norm_num)
  have heq : Complex.Gamma =ᶠ[𝓝 (1 : ℂ)] Complex.GammaIntegral := by
    have hopen : IsOpen {s : ℂ | 0 < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℂ) ∈ {s : ℂ | 0 < s.re})] with s hs
    exact Complex.Gamma_eq_integral hs
  simpa using (hd.congr_of_eventuallyEq heq).unique Complex.hasDerivAt_Gamma_one

lemma gamma_log_integral :
    (∫ t : ℝ in Ioi 0, Real.log t * Real.exp (-t)) = -Real.eulerMascheroniConstant := by
  apply Complex.ofReal_injective
  simpa only [← integral_complex_ofReal, Complex.ofReal_neg] using gamma_log_integral_complex

lemma log_exp_integrable :
    IntegrableOn (fun t : ℝ => Real.log t * Real.exp (-t)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [gamma_log_integral]
  have := Real.one_half_lt_eulerMascheroniConstant
  linarith

lemma quotient_hasSum (t : ℝ) (ht : t ≠ 0) :
    HasSum (fun n : ℕ => (-1 : ℝ)^n * t^n / ((n+1).factorial : ℝ))
      ((1 - Real.exp (-t)) / t) := by
  have hs : HasSum (fun n : ℕ => (-t)^n / (n.factorial : ℝ)) (Real.exp (-t)) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (-t)
  have hs' := (hasSum_nat_add_iff' 1).mpr hs
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one] at hs'
  convert! hs'.mul_left (-1 / t) using 1
  · funext n
    rw [pow_succ, neg_pow]
    field_simp [ht]
    ring
  · ring

lemma quotient_series_integral :
    HasSum (fun n : ℕ => (-1 : ℝ)^n /
      (((n+1 : ℕ) : ℝ) * ((n+1).factorial : ℝ)))
      (∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t) := by
  have hbound : Summable (fun n : ℕ => (1 : ℝ) / ((n+1).factorial : ℝ)) := by
    simpa using (summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial 1)
  have hi := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 1) (μ := volume)
    (F := fun n : ℕ => fun t : ℝ => (-1 : ℝ)^n * t^n / ((n+1).factorial : ℝ))
    (f := fun t : ℝ => (1 - Real.exp (-t)) / t)
    (fun n (_ : ℝ) => (1 : ℝ) / ((n+1).factorial : ℝ))
    (fun n => by fun_prop)
    (fun n => Filter.Eventually.of_forall fun t ht => by
      have ht' : 0 < t ∧ t ≤ 1 := by simpa using ht
      simp only [norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        one_mul, Nat.abs_cast]
      gcongr
      exact pow_le_one₀ (abs_nonneg t) (abs_le.mpr ⟨by linarith, ht'.2⟩))
    (Filter.Eventually.of_forall fun _ _ => hbound)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t ht => quotient_hasSum t (by
      have ht' : 0 < t ∧ t ≤ 1 := by simpa using ht
      exact ht'.1.ne'))
  convert! hi using 1
  funext n
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.cast_add, Nat.cast_one]
  field_simp

lemma ein_one_integral :
    EulerMascheroni.Mixed.ein 1 =
      ((∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t : ℝ) : ℂ) := by
  have h := Complex.ofRealCLM.hasSum quotient_series_integral
  simpa [EulerMascheroni.Mixed.ein] using h.tsum_eq

lemma quotient_bounds (t : ℝ) (ht : 0 < t) :
    0 ≤ (1 - Real.exp (-t)) / t ∧ (1 - Real.exp (-t)) / t ≤ 1 := by
  constructor
  · apply div_nonneg _ ht.le
    have : Real.exp (-t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    linarith
  · apply (div_le_one ht).mpr
    have := Real.add_one_le_exp (-t)
    linarith

lemma quotient_integrable :
    IntervalIntegrable (fun t : ℝ => (1 - Real.exp (-t)) / t) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  refine ((intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ))
    volume 0 1).1).mono'
    (((measurable_const.sub (Real.measurable_exp.comp measurable_neg)).div
      measurable_id).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (quotient_bounds t ht.1).1]
  exact (quotient_bounds t ht.1).2

lemma head_log_integrable :
    IntervalIntegrable (fun t : ℝ => Real.log t * Real.exp (-t)) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact log_exp_integrable.mono_set Ioc_subset_Ioi_self

lemma head_primitive_zero :
    Tendsto (fun t : ℝ => (1 - Real.exp (-t)) * Real.log t) (𝓝[>] 0) (𝓝 0) := by
  have hd : HasDerivAt (fun t : ℝ => 1 - Real.exp (-t)) 1 0 := by
    convert! (((hasDerivAt_id (0 : ℝ)).neg.exp).const_sub 1) using 1 <;> simp
  have hq : Tendsto (fun t : ℝ => (1 - Real.exp (-t)) / t) (𝓝[>] 0) (𝓝 1) := by
    simpa [div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right
  have hl : Tendsto (fun t : ℝ => Real.log t * t) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_log_mul_rpow_nhdsGT_zero (r := (1 : ℝ)) zero_lt_one
  have hh := hq.mul hl
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := (show 0 < t from ht).ne'
  field_simp

lemma head_integral :
    (∫ t in (0 : ℝ)..1, Real.log t * Real.exp (-t)) =
      -(∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t) := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (f := fun t : ℝ => (1 - Real.exp (-t)) * Real.log t)
    (f' := fun t : ℝ => Real.log t * Real.exp (-t) + (1 - Real.exp (-t)) / t)
    (fa := 0) (fb := 0) (by norm_num : (0 : ℝ) < 1)
    (fun t ht => by
      convert! ((((hasDerivAt_id t).neg.exp).const_sub 1).mul
        (Real.hasDerivAt_log ht.1.ne')) using 1 <;> simp <;> ring)
    (head_log_integrable.add quotient_integrable) head_primitive_zero
    (by simpa using (show ContinuousAt (fun t : ℝ => (1 - Real.exp (-t)) * Real.log t) 1 by
          fun_prop (disch := norm_num)).tendsto.mono_left nhdsWithin_le_nhds)
  rw [intervalIntegral.integral_add head_log_integrable quotient_integrable] at hi
  linarith

lemma translated_tail_integral (f : ℝ → ℝ) :
    (∫ t in Ioi (1 : ℝ), f t) = ∫ u in Ioi (0 : ℝ), f (u + 1) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self ((Ioi (1 : ℝ)).indicator f) 1]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u
  dsimp only
  by_cases hu : 0 < u
  · rw [indicator_of_mem (show u + 1 ∈ Ioi (1 : ℝ) by simp; linarith),
      indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu)]
  · rw [indicator_of_notMem (show u + 1 ∉ Ioi (1 : ℝ) by simp; linarith),
      indicator_of_notMem (show u ∉ Ioi (0 : ℝ) from hu)]

lemma tail_reciprocal_integral :
    (∫ t : ℝ in Ioi 1, Real.exp (-t) / t) =
      EulerMascheroni.gompertzConstant / Real.exp 1 := by
  rw [translated_tail_integral]
  have heq : (fun u : ℝ => Real.exp (-(u+1)) / (u+1)) =
      fun u : ℝ => (Real.exp (-u) / (1+u)) / Real.exp 1 := by
    funext u
    rw [neg_add, Real.exp_add, Real.exp_neg 1]
    ring
  rw [heq, integral_div]
  rfl

lemma tail_reciprocal_integrable :
    IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Ioi 1) := by
  refine (integrableOn_exp_neg_Ioi 1).mono'
    ((Real.measurable_exp.comp measurable_neg).div measurable_id).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : 0 < t := lt_trans zero_lt_one ht
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.exp_pos _).le ht'.le)]
  exact div_le_self (Real.exp_pos _).le ht.le

lemma tail_log_integrable :
    IntegrableOn (fun t : ℝ => Real.log t * Real.exp (-t)) (Ioi 1) :=
  log_exp_integrable.mono_set (Ioi_subset_Ioi (by norm_num))

lemma tail_primitive_zero :
    Tendsto (fun t : ℝ => Real.exp (-t) * Real.log t) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact mul_nonneg (Real.exp_pos _).le (Real.log_nonneg ht)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [pow_one, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one ht)
    linarith

lemma tail_integral :
    (∫ t : ℝ in Ioi 1, Real.log t * Real.exp (-t)) =
      EulerMascheroni.gompertzConstant / Real.exp 1 := by
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun t : ℝ => Real.exp (-t) * Real.log t)
    (f' := fun t : ℝ => Real.exp (-t) / t - Real.log t * Real.exp (-t))
    (a := 1) (m := 0)
    (show ContinuousWithinAt (fun t : ℝ => Real.exp (-t) * Real.log t) (Ici 1) 1 from
      (show ContinuousAt (fun t : ℝ => Real.exp (-t) * Real.log t) 1 by fun_prop (disch := norm_num)).continuousWithinAt)
    (fun t ht => by
      have ht' : t ≠ 0 := (lt_trans zero_lt_one ht).ne'
      convert! ((hasDerivAt_id t).neg.exp).mul (Real.hasDerivAt_log ht') using 1 <;>
        simp <;> ring)
    (tail_reciprocal_integrable.sub tail_log_integrable) tail_primitive_zero
  rw [integral_sub tail_reciprocal_integrable tail_log_integrable,
    tail_reciprocal_integral] at hi
  simp only [Real.log_one, mul_zero, sub_zero] at hi
  linarith

lemma hardy_identity :
    EulerMascheroni.Mixed.ein 1 = (Real.eulerMascheroniConstant : ℂ) +
      (EulerMascheroni.gompertzConstant : ℂ) / Complex.exp 1 := by
  have hi := intervalIntegral.integral_interval_add_Ioi log_exp_integrable tail_log_integrable
  rw [head_integral, tail_integral, gamma_log_integral] at hi
  have hr : (∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t) =
      Real.eulerMascheroniConstant + EulerMascheroni.gompertzConstant / Real.exp 1 := by
    linarith
  rw [ein_one_integral, hr]
  simp

end HardyFormalization

theorem solution :
    EulerMascheroni.Mixed.ein 1 = (Real.eulerMascheroniConstant : ℂ) +
      (EulerMascheroni.gompertzConstant : ℂ) / Complex.exp 1 :=
  HardyFormalization.hardy_identity

#print axioms solution
