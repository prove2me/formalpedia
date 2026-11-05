-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_ruin_clock_finite_infinite_horizon_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:22:56.3032+00:00
-- url     : https://prove2.me/submissions/bcafab81-0b6b-432b-b2d4-c92ce32d0064

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact finite-ruin saturation and infinite-ruin horizon growth of
the actual source bounded original ruin clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    ∀ ω : Ω,
      (ruinTime X x D ω ≠ ⊤ →
        ∀ T : ℝ≥0, (ruinTime X x D ω).toNNReal ≤ T →
          (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal =
            (ruinTime X x D ω).toNNReal) ∧
      (ruinTime X x D ω = ⊤ →
        ∀ T : ℝ≥0,
          (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal = T) := by
  intro ω
  constructor
  · intro hRuinFinite T hT
    have hBound : ruinTime X x D ω ≤ (T : ℝ≥0∞) := by
      calc
        ruinTime X x D ω =
          ((ruinTime X x D ω).toNNReal : ℝ≥0∞) :=
            (ENNReal.coe_toNNReal hRuinFinite).symm
        _ ≤ (T : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hT
    rw [min_eq_left hBound]
  · intro hRuinTop T
    simp [hRuinTop]
