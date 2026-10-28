-- Prove2me | solution 1 for AvramDividend.Classical.bv_strict_zero_ruin_deficit_increment_band_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:06:32.151378+00:00
-- url     : https://prove2.me/submissions/e2eed56c-e99b-490e-903e-514e17cc8612

import Theorems.Thm_AvramDividend_Classical_zero_reflected_ruin_strict_survival_capital_monotone_prefix
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Before genuine zero-barrier ruin, each increment of the actual
    bounded-variation drift deficit lies between zero and linear drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      (T : ℝ≥0∞) < barrierRuinTime X 0 ω →
      ∀ s u : ℝ≥0, s ≤ u → u ≤ T →
      0 ≤ (X.drift * (u : ℝ) - X.X u ω) -
        (X.drift * (s : ℝ) - X.X s ω) ∧
      (X.drift * (u : ℝ) - X.X u ω) -
        (X.drift * (s : ℝ) - X.X s ω) ≤
          X.drift * ((u : ℝ) - (s : ℝ)) := by
  refine (bv_drift_deficit_ae_monotone_all_times X hBV).mono ?_
  intro ω hMono T hBefore s u hsu huT
  have hCapital :=
    zero_reflected_ruin_strict_survival_capital_monotone_prefix
      X ω T hBefore s u hsu huT
  constructor
  · exact sub_nonneg.mpr (hMono hsu)
  · calc
      (X.drift * (u : ℝ) - X.X u ω) -
          (X.drift * (s : ℝ) - X.X s ω) =
        X.drift * ((u : ℝ) - (s : ℝ)) -
          (X.X u ω - X.X s ω) := by ring
      _ ≤ X.drift * ((u : ℝ) - (s : ℝ)) :=
        sub_le_self _ (sub_nonneg.mpr hCapital)
