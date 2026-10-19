-- Prove2me | solution 1 for AvramDividend.Classical.firstUpcrossing_reflectedSup_eventually_lt_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T11:08:38.166255+00:00
-- url     : https://prove2.me/submissions/2fcf4476-c46f-428d-aa83-c420b02e5ea2

import Mathlib.Topology.Order.Basic
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞)))
    (hRight : ContinuousWithinAt (fun t => reflectedSup X t ω)
      (Set.Ici u) u) :
    ∀ᶠ t in 𝓝[≥] u, reflectedSup X t ω < a := by
  have hZero : reflectedSup X u ω = 0 := by
    exact firstUpcrossing_runningSup_sub_path_eq_zero X b hb ω u hu
  have hLt : reflectedSup X u ω < a := by
    simpa [hZero] using ha
  exact hRight.tendsto.eventually (Iio_mem_nhds hLt)
