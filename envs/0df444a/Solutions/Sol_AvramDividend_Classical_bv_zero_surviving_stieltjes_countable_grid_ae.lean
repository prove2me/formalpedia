-- Prove2me | solution 1 for AvramDividend.Classical.bv_zero_surviving_stieltjes_countable_grid_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T16:46:00.406175+00:00
-- url     : https://prove2.me/submissions/e565148c-8fae-43d3-9462-5615582d70eb

import Theorems.Thm_AvramDividend_Classical_bv_zero_surviving_weighted_stieltjes_prefix_ae
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.MeasurableSpace.Defs
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A single almost-sure event supports the finite-activity zero-barrier
weighted Stieltjes reward formula at every time in any countable grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (grid : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      ((grid n : ℝ≥0) : ℝ≥0∞) < barrierRuinTime X 0 ω →
      ∀ f : ℝ → ℝ≥0∞,
        (∫⁻ t in Ioc (0 : ℝ) ((grid n : ℝ≥0) : ℝ), f t
          ∂(dividendMeasure (runningSup X) ω)) =
        (∫⁻ t in Ioc (0 : ℝ) ((grid n : ℝ≥0) : ℝ), f t
          ∂((ENNReal.ofReal X.drift) • volume)) := by
  exact (ae_all_iff).mpr fun n =>
    bv_zero_surviving_weighted_stieltjes_prefix_ae
      X hStanding hBV hFinite (grid n)
