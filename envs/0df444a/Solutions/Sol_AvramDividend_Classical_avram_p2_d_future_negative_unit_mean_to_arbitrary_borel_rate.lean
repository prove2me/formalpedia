-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_negative_unit_mean_to_arbitrary_borel_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:19:41.680642+00:00
-- url     : https://prove2.me/submissions/83345805-4951-4edb-aef5-ca1eb1c605e8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_general_interval_all_real_source_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_arbitrary_borel_rate_of_negative_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Negative Borel identification at unit time suffices for all original
times and all Borel marks; the unsolved unit identification is explicit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hunitNegative : ∀ (C : Set ℝ), MeasurableSet C →
      C ⊆ Iio (0 : ℝ) → (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ C) ∂P) = X.ν C) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) = ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  apply avram_p2_d_future_arbitrary_borel_rate_of_negative_rate
    X s t hst B hB
  calc
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∩ Iio (0 : ℝ))) ∂P) =
        ((t - s : ℝ≥0) : ℝ≥0∞) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ (B ∩ Iio (0 : ℝ))) ∂P) :=
      avram_p2_d_future_original_general_interval_all_real_source_rate
        X s t hst (B ∩ Iio (0 : ℝ)) (hB.inter isOpen_Iio.measurableSet)
    _ = ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B ∩ Iio (0 : ℝ)) := by
      rw [hunitNegative (B ∩ Iio (0 : ℝ))
        (hB.inter isOpen_Iio.measurableSet) inter_subset_right]
