-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_future_band_squared_count_stronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:30:32.405484+00:00
-- url     : https://prove2.me/submissions/1afb139d-d606-484d-8606-fbc4f5439cde

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Future measurability of the original intrinsic marked count yields
strong measurability of the squared centred source count. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (N : Ω → ℝ≥0∞)
    (hSource : ∀ ω, N ω =
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B))
    (r : ℝ) (hRate : r =
      ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal)
    (mFuture : MeasurableSpace Ω)
    (hNmeas : Measurable[mFuture] N) :
    StronglyMeasurable[mFuture] (fun ω => ((N ω).toReal - r) ^ 2) := by
  have hReal : Measurable[mFuture] (fun ω => (N ω).toReal) :=
    ENNReal.measurable_toReal.comp hNmeas
  exact ((hReal.sub measurable_const).pow_const 2).stronglyMeasurable
