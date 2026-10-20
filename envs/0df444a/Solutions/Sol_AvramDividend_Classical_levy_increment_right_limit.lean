-- Prove2me | solution 1 for AvramDividend.Classical.levy_increment_right_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:18:24.639803+00:00
-- url     : https://prove2.me/submissions/62a0e7c9-fc93-407a-9635-9c5db46f6af1

import Mathlib.Topology.Algebra.Order.Field
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) :
    Tendsto
      (fun u : ℝ≥0 => X.X t ω - X.X u ω)
      (𝓝[>] s)
      (𝓝 (X.X t ω - X.X s ω)) := by
  have hX : Tendsto (fun u : ℝ≥0 => X.X u ω)
      (𝓝[>] s) (𝓝 (X.X s ω)) :=
    ((X.rightCont ω s).mono Ioi_subset_Ici_self).tendsto
  exact tendsto_const_nhds.sub hX
