-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_uniform_drift_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:39:01.532224+00:00
-- url     : https://prove2.me/submissions/5e25468c-7b96-4a9f-8c0e-b34ccf4c358f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_simultaneous_all_clock_strict_preruin_prepayment_drift_strip

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A bounded random source clock lies in a uniform deterministic prepayment
    reserve strip on one source event; no stopping-time assumption is needed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hXzero : ∀ ω, X.X 0 ω = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (H : ℝ≥0) (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ H) :
    ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ riskProcess X x D (τ ω) ω ∧
      riskProcess X x D (τ ω) ω ≤
        x + (H : ℝ) * max X.drift 0 := by
  filter_upwards
    [avram_p3_g2_original_BV_simultaneous_all_clock_strict_preruin_prepayment_drift_strip
      X hBV hXzero x D hD] with ω hω
  intro hsurvive
  obtain ⟨hlo, hup⟩ := hω (τ ω) hsurvive
  have ht : (τ ω : ℝ) ≤ (H : ℝ) := by
    exact_mod_cast hτBound ω
  have hn : 0 ≤ (τ ω : ℝ) := NNReal.coe_nonneg _
  have hd : 0 ≤ max X.drift 0 := le_max_right _ _
  have hbounded :
      (τ ω : ℝ) * X.drift ≤ (H : ℝ) * max X.drift 0 := by
    calc
      (τ ω : ℝ) * X.drift ≤ (τ ω : ℝ) * max X.drift 0 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) hn
      _ ≤ (H : ℝ) * max X.drift 0 :=
        mul_le_mul_of_nonneg_right ht hd
  refine ⟨hlo, ?_⟩
  linarith
