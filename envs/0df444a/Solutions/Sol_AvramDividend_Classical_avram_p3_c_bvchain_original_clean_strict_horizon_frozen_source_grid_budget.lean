-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_clean_strict_horizon_frozen_source_grid_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:39:41.679931+00:00
-- url     : https://prove2.me/submissions/7850377e-ff6a-430d-abd3-2ea000605e9d

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_hybrid_strict_horizon_discounted_grid_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_discount_stieltjes_clock_correction_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_bv_caplinear_postpayment_candidate_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_corrected_positive_cap_bv_postpayment_value_nonnegative_automatic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Original strict-horizon hybrid BV grid budget with every nonpositive
discount-clock correction removed by the original candidate hypotheses. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (C : ℝ≥0∞) (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
      w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (n : ℕ) (hzero : u 0 = 0)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (hPre : ∀ i : ℕ, i < n → (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (b : ℝ≥0) (hFinal : u n < b)
    (hBPre : (b : ℝ≥0∞) < ruinTime X x D ω) :
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let cash : ℕ → ℝ := fun i => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Ioc (u i : ℝ) (u (i + 1) : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let source : ℕ → ℝ := fun i => V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    let finalCash : ℝ := (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Ioo (u n : ℝ) (b : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    rightLimit D 0 ω + (∑ i ∈ Finset.range n, cash i) + finalCash +
      Real.exp (-(q * (b : ℝ))) * w (riskProcess X x D b ω) ≤
      w x + (∑ i ∈ Finset.range n, e i * source i) +
      e n * (V (x + X.X b ω - rightLimit D (u n) ω) -
        V (x + X.X (u n) ω - rightLimit D (u n) ω)) := by
  let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
  let post : ℕ → ℝ := fun i => V (x + X.X (u i) ω - rightLimit D (u i) ω)
  have hpost (i : ℕ) (hi : i < n) : 0 ≤ post (i + 1) := by
    exact avram_wave5_03_original_bv_caplinear_postpayment_candidate_nonnegative
      X w V C hC hw0 hw_cont hw_neg hw_smooth hw_grad hVtop hVfinite
      x hx hxc D hD ω (u (i + 1))
  have hbpos : 0 < b := lt_of_le_of_lt (show (0 : ℝ≥0) ≤ u n by exact bot_le) hFinal
  have hterm : 0 ≤ w (riskProcess X x D b ω) :=
    avram_wave7_09_corrected_positive_cap_bv_postpayment_value_nonnegative_automatic
      X C hC w hw_cont hw0 hw_smooth hw_grad x hxc D hD ω b hbpos hBPre
  have hClock := avram_p3_c_bvchain_discount_stieltjes_clock_correction_nonpos
    q hq u n hGrid b (le_of_lt hFinal) post
    (w (riskProcess X x D b ω)) hpost hterm
  let cash : ℕ → ℝ := fun i => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
    Ioc (u i : ℝ) (u (i + 1) : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let source : ℕ → ℝ := fun i => V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
    V (x + X.X (u i) ω - rightLimit D (u i) ω)
  let finalCash : ℝ := (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
    Ioo (u n : ℝ) (b : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  have hBudget := avram_p3_c_bvchain_original_hybrid_strict_horizon_discounted_grid_budget
    X x C hC hxc w V hw_cont hw_smooth hw_grad hVtop hVfinite D hD hjump
    ω q hq u n hzero hGrid hPre b hFinal hBPre
  dsimp only at hBudget hClock ⊢
  nlinarith only [hBudget, hClock]
