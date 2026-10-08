-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_continuousAt_away_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:33:40.409986+00:00
-- url     : https://prove2.me/submissions/f7b5081a-1741-4495-b013-73164d28bf1e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (z : ℝ) (hz : z ≠ 0) :
    ContinuousAt W z := by
  by_cases hn : z < 0
  · have hnmem : Iio (0 : ℝ) ∈ 𝓝 z :=
      isOpen_Iio.mem_nhds hn
    have hev : W =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [hnmem] with w hw
      exact hW.1 w hw
    exact continuousAt_const.congr_of_eventuallyEq hev
  · have hz0 : 0 ≤ z := le_of_not_gt hn
    have hzpos : 0 < z := lt_of_le_of_ne hz0 (Ne.symm hz)
    have hnmem : Ici (0 : ℝ) ∈ 𝓝 z := by
      apply Filter.mem_of_superset (isOpen_Ioi.mem_nhds hzpos)
      intro w hw
      exact le_of_lt (by simpa only [mem_Ioi] using hw)
    exact hW.2.2.1.continuousAt hnmem
