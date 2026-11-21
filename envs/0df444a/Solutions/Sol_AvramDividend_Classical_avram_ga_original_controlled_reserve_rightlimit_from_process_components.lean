-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_controlled_reserve_rightlimit_from_process_components
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:32:05.347384+00:00
-- url     : https://prove2.me/submissions/1fdad27b-1fdc-4cdc-a926-21f3e04bd4c9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Filter Topology Set MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0)
    (hX : Tendsto (fun u : ℝ≥0 => X.X u ω)
      (𝓝[>] t) (𝓝 (X.X t ω)))
    (hD : Tendsto (fun u : ℝ≥0 => D u ω)
      (𝓝[>] t) (𝓝 (rightLimit D t ω))) :
    Tendsto (fun u : ℝ≥0 => riskProcess X x D u ω)
      (𝓝[>] t)
      (𝓝 (x + X.X t ω - rightLimit D t ω)) := by
  have hsum := hX.const_add x
  have hlim := hsum.sub hD
  simpa only [riskProcess] using hlim
