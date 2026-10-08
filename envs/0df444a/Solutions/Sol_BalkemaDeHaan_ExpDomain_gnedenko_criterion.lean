-- Prove2me | solution 1 for BalkemaDeHaan.ExpDomain.gnedenko_criterion
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:26:00.12638+00:00
-- url     : https://prove2.me/submissions/32630a26-8839-4a36-a66a-8bc71dc3ecf7

import Definitions.Def_BalkemaDeHaan_ExpDomain_Domains



namespace BalkemaDeHaan.ExpDomain

open Filter MeasureTheory ProbabilityTheory Topology

lemma tail_eq_one_sub_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] (y : ℝ) :
    BalkemaDeHaan.LimitTypes.tail μ y = 1 - cdf μ y := by
  unfold BalkemaDeHaan.LimitTypes.tail
  rw [cdf_eq_real, measureReal_def, ← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]

lemma log_one_sub_bounds {u : ℝ} (hu1 : u < 1) :
    -u / (1 - u) ≤ Real.log (1 - u) ∧ Real.log (1 - u) ≤ -u := by
  have h1 : 0 < 1 - u := by linarith
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos h1
    have h2 : 1 - (1 - u)⁻¹ = -u / (1 - u) := by
      field_simp
      ring
    linarith
  · have := Real.log_le_sub_one_of_pos h1
    linarith

lemma continuous_lambdaLaw : Continuous lambdaLaw := by
  unfold lambdaLaw
  fun_prop

/-- Gnedenko's lemma: `F_n^n → e^{-τ}` iff `n (1 - F_n) → τ`, for `τ > 0`, `F_n ∈ [0,1]`. -/
lemma pow_tendsto_iff (F : ℕ → ℝ) (hF0 : ∀ n, 0 ≤ F n) (hF1 : ∀ n, F n ≤ 1) (τ : ℝ) (hτ : 0 < τ) :
    Tendsto (fun n : ℕ => (F n) ^ n) atTop (𝓝 (Real.exp (-τ))) ↔
    Tendsto (fun n : ℕ => (n : ℝ) * (1 - F n)) atTop (𝓝 τ) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  constructor
  · intro h
    -- eventually F n ^ n > 0
    have hpos : ∀ᶠ n in atTop, 0 < F n ^ n := h.eventually (lt_mem_nhds (Real.exp_pos _))
    have hFpos : ∀ᶠ n in atTop, 0 < F n := by
      filter_upwards [hpos, eventually_ge_atTop 1] with n hn hn1
      rcases (hF0 n).lt_or_eq with h' | h'
      · exact h'
      · exfalso
        rw [← h', zero_pow (by omega)] at hn
        exact lt_irrefl _ hn
    -- n log F n → -τ
    have hlog : Tendsto (fun n : ℕ => (n : ℝ) * Real.log (F n)) atTop (𝓝 (-τ)) := by
      have := (Real.continuousAt_log (Real.exp_pos (-τ)).ne').tendsto.comp h
      rw [Real.log_exp] at this
      refine this.congr' ?_
      filter_upwards with n
      simp [Function.comp, Real.log_pow]
    -- log F n → 0
    have hlog0 : Tendsto (fun n => Real.log (F n)) atTop (𝓝 0) := by
      have := hlog.div_atTop hnat
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : (n : ℝ) ≠ 0 := by positivity
      field_simp
    -- F n → 1
    have hF : Tendsto F atTop (𝓝 1) := by
      have := (Real.continuous_exp.tendsto 0).comp hlog0
      rw [Real.exp_zero] at this
      refine this.congr' ?_
      filter_upwards [hFpos] with n hn
      simp [Function.comp, Real.exp_log hn]
    -- squeeze
    have hup : Tendsto (fun n : ℕ => -((n : ℝ) * Real.log (F n))) atTop (𝓝 τ) := by
      have := hlog.neg
      simpa using this
    have hlow : Tendsto (fun n : ℕ => F n * (-((n : ℝ) * Real.log (F n)))) atTop (𝓝 τ) := by
      have := hF.mul hup
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
    · filter_upwards [hFpos] with n hn
      obtain ⟨h1, _⟩ := log_one_sub_bounds (u := 1 - F n) (by linarith)
      have e : (1 : ℝ) - (1 - F n) = F n := by ring
      rw [e] at h1
      have h1' : -(1 - F n) ≤ Real.log (F n) * F n := by
        rw [div_le_iff₀ hn] at h1
        exact h1
      have hn0 : (0 : ℝ) ≤ n := by positivity
      nlinarith
    · filter_upwards [hFpos] with n hn
      obtain ⟨_, h2⟩ := log_one_sub_bounds (u := 1 - F n) (by linarith)
      have e : (1 : ℝ) - (1 - F n) = F n := by ring
      rw [e] at h2
      have hn0 : (0 : ℝ) ≤ n := by positivity
      nlinarith
  · intro h
    -- u n → 0
    have hu : Tendsto (fun n => 1 - F n) atTop (𝓝 0) := by
      have := h.div_atTop hnat
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : (n : ℝ) ≠ 0 := by positivity
      field_simp
    have hFpos : ∀ᶠ n in atTop, 0 < F n := by
      have := hu.eventually (gt_mem_nhds (show (0:ℝ) < 1/2 by norm_num))
      filter_upwards [this] with n hn
      linarith
    have hF : Tendsto F atTop (𝓝 1) := by
      have := hu.const_sub 1
      simpa using this
    -- n log F n → -τ by squeeze
    have hup : Tendsto (fun n : ℕ => -((n : ℝ) * (1 - F n))) atTop (𝓝 (-τ)) := h.neg
    have hlow : Tendsto (fun n : ℕ => -((n : ℝ) * (1 - F n)) / F n) atTop (𝓝 (-τ)) := by
      have := hup.div hF one_ne_zero
      rw [div_one] at this
      exact this
    have hlog : Tendsto (fun n : ℕ => (n : ℝ) * Real.log (F n)) atTop (𝓝 (-τ)) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
      · filter_upwards [hFpos] with n hn
        obtain ⟨h1, _⟩ := log_one_sub_bounds (u := 1 - F n) (by linarith)
        have e : (1 : ℝ) - (1 - F n) = F n := by ring
        rw [e] at h1
        have hn0 : (0 : ℝ) ≤ n := by positivity
        rw [div_le_iff₀ hn] at h1 ⊢
        have : -((n:ℝ) * (1 - F n)) = n * (-(1 - F n)) := by ring
        rw [this]
        have := mul_le_mul_of_nonneg_left h1 hn0
        linarith
      · filter_upwards [hFpos] with n hn
        obtain ⟨_, h2⟩ := log_one_sub_bounds (u := 1 - F n) (by linarith)
        have e : (1 : ℝ) - (1 - F n) = F n := by ring
        rw [e] at h2
        have hn0 : (0 : ℝ) ≤ n := by positivity
        nlinarith
    have := (Real.continuous_exp.tendsto _).comp hlog
    refine this.congr' ?_
    filter_upwards [hFpos] with n hn
    simp only [Function.comp]
    rw [← Real.log_pow, Real.exp_log (pow_pos hn n)]

theorem gnedenko_core (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n) :
    WeakConvergenceNat (fun n x => (cdf μ (a n * x + b n)) ^ n) lambdaLaw ↔
      TailScaledConvergence μ a b Set.univ := by
  unfold WeakConvergenceNat TailScaledConvergence
  have hL : ∀ x, ContinuousAt lambdaLaw x := fun x => continuous_lambdaLaw.continuousAt
  constructor
  · intro h x _
    have := h x (hL x)
    unfold lambdaLaw at this
    rw [pow_tendsto_iff _ (fun n => cdf_nonneg μ _) (fun n => cdf_le_one μ _) _ (Real.exp_pos _)] at this
    refine this.congr' ?_
    filter_upwards with n
    rw [tail_eq_one_sub_cdf]
    ring_nf
  · intro h x _
    have := h x (Set.mem_univ x)
    unfold lambdaLaw
    rw [pow_tendsto_iff _ (fun n => cdf_nonneg μ _) (fun n => cdf_le_one μ _) _ (Real.exp_pos _)]
    refine this.congr' ?_
    filter_upwards with n
    rw [tail_eq_one_sub_cdf]
    ring_nf

end BalkemaDeHaan.ExpDomain

open BalkemaDeHaan.ExpDomain
open Filter MeasureTheory ProbabilityTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n) :
    WeakConvergenceNat (fun n x => (cdf μ (a n * x + b n)) ^ n) lambdaLaw ↔
      TailScaledConvergence μ a b Set.univ := by
  exact gnedenko_core μ a b ha
