-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_terminal_L1_of_source_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:10:28.015009+00:00
-- url     : https://prove2.me/submissions/240c3a39-b81d-42f8-bf18-c5f491b7a26c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_continuous_test_abs_le_on_finite_cap
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_uniform_drift_strip

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine strict-survival prepayment terminal is L1 under verified
    measurability of random-time reserve and survival, using uniform BV drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hXzero : ∀ ω, X.X 0 ω = 0)
    (hFinite : IsFiniteMeasure P)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hwCont : ContinuousOn w (Ici 0))
    (hwMeas : Measurable w)
    (q : ℝ) (hq : 0 ≤ q)
    (H : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτMeas : Measurable τ) (hτBound : ∀ ω, τ ω ≤ H)
    (hRiskMeas : Measurable (fun ω =>
      riskProcess X x D (τ ω) ω))
    (hSurvivalMeas : MeasurableSet {ω |
      (τ ω : ℝ≥0∞) < ruinTime X x D ω}) :
    Integrable (fun ω => if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * (τ ω : ℝ))) *
        w (riskProcess X x D (τ ω) ω)
    else 0) P := by
  classical
  letI : IsFiniteMeasure P := hFinite
  let B : ℝ := x + (H : ℝ) * max X.drift 0
  have hB : 0 ≤ B :=
    add_nonneg hx (mul_nonneg (NNReal.coe_nonneg _) (le_max_right _ _))
  obtain ⟨M, hM0, hM⟩ :=
    continuous_test_abs_le_on_finite_cap w B hB hwCont
  have hExpMeas : Measurable
      (fun ω : Ω => Real.exp (-(q * (τ ω : ℝ)))) := by
    fun_prop
  have hMeas : Measurable (fun ω => if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * (τ ω : ℝ))) *
        w (riskProcess X x D (τ ω) ω)
    else 0) :=
    (hExpMeas.mul (hwMeas.comp hRiskMeas)).ite
      hSurvivalMeas measurable_const
  have hstrip := avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_uniform_drift_strip
    X hBV hXzero x D hD H τ hτBound
  have hBound : ∀ᵐ ω ∂P, ‖((fun ω => if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * (τ ω : ℝ))) *
        w (riskProcess X x D (τ ω) ω)
    else 0)) ω‖ ≤ M := by
    filter_upwards [hstrip] with ω hω
    by_cases hs : (τ ω : ℝ≥0∞) < ruinTime X x D ω
    · obtain ⟨hlo, hhi⟩ := hω hs
      have hDisc : Real.exp (-(q * (τ ω : ℝ))) ≤ 1 :=
        Real.exp_le_one_iff.mpr
          (neg_nonpos.mpr (mul_nonneg hq (NNReal.coe_nonneg _)))
      have hW := hM (riskProcess X x D (τ ω) ω) hlo hhi
      simp only [hs, ↓reduceIte, Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-(q * (τ ω : ℝ))) *
            |w (riskProcess X x D (τ ω) ω)| ≤
          1 * |w (riskProcess X x D (τ ω) ω)| :=
            mul_le_mul_of_nonneg_right hDisc (abs_nonneg _)
        _ ≤ M := by simpa using hW
    · simp only [hs, ↓reduceIte, norm_zero]
      exact hM0
  exact (integrable_const M).mono' hMeas.aestronglyMeasurable hBound
