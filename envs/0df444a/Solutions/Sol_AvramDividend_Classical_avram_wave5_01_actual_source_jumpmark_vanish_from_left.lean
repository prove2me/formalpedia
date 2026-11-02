-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_jumpmark_vanish_from_left
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:36:06.837104+00:00
-- url     : https://prove2.me/submissions/6aca7c0b-d3a8-4eb3-8569-265ae9fbf358

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuine source jump mark vanishes along times approaching any positive
deterministic clock from below, for every original sample path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    Tendsto
      (fun u : ℝ≥0 =>
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
      (𝓝[<] t) (𝓝 (0 : ℝ)) := by
  have hleft :
      Tendsto (fun u : ℝ≥0 => X.X u ω) (𝓝[<] t)
        (𝓝 (Function.leftLim (fun u : ℝ≥0 => X.X u ω) t)) :=
    tendsto_leftLim_of_tendsto (X.leftLim ω t ht)
  have hpre :
      ContinuousWithinAt
        (fun u : ℝ≥0 => Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
        (Iic t) t :=
    continuousWithinAt_leftLim_Iic hleft
  have hsubset : (Iio t : Set ℝ≥0) ⊆ Iic t :=
    Set.Iio_subset_Iic_self
  have hpre' :
      Tendsto
        (fun u : ℝ≥0 => Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
        (𝓝[<] t)
        (𝓝 (Function.leftLim (fun u : ℝ≥0 => X.X u ω) t)) :=
    hpre.mono_left (nhdsWithin_mono t hsubset)
  simpa only [sub_self] using hleft.sub hpre'
