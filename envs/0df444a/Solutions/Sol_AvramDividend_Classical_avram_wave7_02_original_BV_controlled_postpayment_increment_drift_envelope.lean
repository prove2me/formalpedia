-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T11:53:05.734346+00:00
-- url     : https://prove2.me/submissions/ecf7f8f9-8525-49ff-83a4-2b2988463038

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- For the original BV Lévy process and genuine right dividend payments,
the full controlled reserve increment is bounded above by physical drift.
This includes all negative source jumps, singular continuous source loss,
diffuse dividends, and simultaneous right dividend jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      (x + X.X t ω - rightLimit D t ω) -
        (x + X.X s ω - rightLimit D s ω) ≤
      ((t : ℝ) - (s : ℝ)) * X.drift := by
  filter_upwards
    [bv_actual_levy_residual_ae_monotone_all_times X hBV] with ω hR
  intro s t hst
  have hSource :
      X.X t ω - X.X s ω ≤ ((t : ℝ) - (s : ℝ)) * X.drift := by
    have hstR := hR hst
    dsimp at hstR
    nlinarith
  have hDividend : rightLimit D s ω ≤ rightLimit D t ω :=
    avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω hst
  linarith
