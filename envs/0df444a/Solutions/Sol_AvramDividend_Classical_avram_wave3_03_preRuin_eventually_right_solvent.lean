-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_preRuin_eventually_right_solvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:40:48.298994+00:00
-- url     : https://prove2.me/submissions/46fbb8c4-21b3-44a8-afe6-9b51887933f6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Strictly pre-ruin capital remains nonnegative on the right germ of time:
the original ruin time is an infimum and the time embedding is continuous. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (hT : (T : ℝ≥0∞) < ruinTime X x D ω) :
    ∀ᶠ s in 𝓝[>] T, 0 ≤ riskProcess X x D s ω := by
  have hcoe : Continuous (fun s : ℝ≥0 => (s : ℝ≥0∞)) := ENNReal.continuous_coe
  have htend : Tendsto (fun s : ℝ≥0 => (s : ℝ≥0∞))
      (𝓝[>] T) (𝓝 (T : ℝ≥0∞)) :=
    (hcoe.tendsto T).mono_left nhdsWithin_le_nhds
  filter_upwards [htend.eventually (isOpen_Iio.mem_nhds hT)] with s hs
  exact riskProcess_nonneg_before_ruin X x D ω s hs