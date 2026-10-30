-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_bv_stopped_scale_continuity_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:23:05.779305+00:00
-- url     : https://prove2.me/submissions/84dce862-0a0b-45a0-b7d1-1ef432423423

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_stopped_min_away_zero_ae
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Actual BV stopped q-scale is continuous at its realised finite two-sided exit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    ∀ᵐ ω ∂P,
      min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω) < ⊤ →
      ContinuousAt W (x + X.X (min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω)).toNNReal ω) := by
  have hnz := avram_ws01b_bv_stopped_min_away_zero_ae
    X hX q hq W hW hBV a x ha hx0 hxa
  filter_upwards [hnz] with ω hω
  intro hfin
  exact scaleFunction_continuousAt_away_zero X q W hW
    (x + X.X (min (twoSidedExitUpTime X (a - x) ω)
      (twoSidedExitDownTime X (-x) ω)).toNNReal ω) (hω hfin)
