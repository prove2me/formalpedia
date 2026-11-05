-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_terminal_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:24:51.853203+00:00
-- url     : https://prove2.me/submissions/cf633290-5019-4744-83e5-1adb09c71a56

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_prepayment_riskProcess_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_measurable_random_clock_strict_ruin_survival_event
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_terminal_L1_of_source_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source-exact random-clock strict prepayment terminal L¹ without measurability assumptions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hXzero : ∀ ω, X.X 0 ω = 0) (hFinite : IsFiniteMeasure P)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hwCont : ContinuousOn w (Ici 0))
    (hwMeas : Measurable w)
    (q : ℝ) (hq : 0 ≤ q)
    (H : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτMeas : Measurable τ) (hτBound : ∀ ω, τ ω ≤ H) :
    Integrable (fun ω => if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * (τ ω : ℝ))) *
        w (riskProcess X x D (τ ω) ω)
    else 0) P := by
  have hPair : Measurable (fun ω : Ω => (τ ω, ω)) :=
    hτMeas.prodMk measurable_id
  have hRisk : Measurable (fun ω : Ω =>
      riskProcess X x D (τ ω) ω) := by
    simpa only [Function.comp_def] using
      (avram_p3_g2_original_prepayment_riskProcess_joint_measurable X x D hD).comp
        hPair
  have hSurv : MeasurableSet {ω : Ω |
      (τ ω : ℝ≥0∞) < ruinTime X x D ω} :=
    avram_p3_g2_original_measurable_random_clock_strict_ruin_survival_event
      X x D hD τ hτMeas
  exact avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_terminal_L1_of_source_measurable
    X hBV hXzero hFinite x hx D hD w hwCont hwMeas
    q hq H τ hτMeas hτBound hRisk hSurv
