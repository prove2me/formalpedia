-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_past_event_future_negative_Borel_mark_count_factor_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:21:32.517203+00:00
-- url     : https://prove2.me/submissions/e06e001a-4de3-476e-aaa9-b52ede9a6ab3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_weighted_rate_from_unconditional
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The future original marked count has an exact conditional first moment against every past event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω *
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      P A * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
  classical
  let W : Ω → ℝ≥0∞ := A.indicator (fun _ => 1)
  have hW : Measurable[𝓕 s] W := measurable_const.indicator hA
  have hRate :=
    avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact
      X s t hst B hB hNeg
  have hWeighted :=
    avram_p2_e_compensator_weighted_rate_from_unconditional
      X s t hst B hB W hW hRate
  have hAMeas : MeasurableSet A := (𝓕.le s) A hA
  have hWA : (∫⁻ ω, W ω ∂P) = P A := by
    change (∫⁻ ω, A.indicator (1 : Ω → ℝ≥0∞) ω ∂P) = P A
    exact lintegral_indicator_one hAMeas
  calc
    _ = (∫⁻ ω, W ω ∂P) *
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := hWeighted
    _ = _ := by rw [hWA]
