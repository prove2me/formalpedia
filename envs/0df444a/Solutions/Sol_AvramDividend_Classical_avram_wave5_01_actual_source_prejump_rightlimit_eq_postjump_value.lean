-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_prejump_rightlimit_eq_postjump_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:42:57.934487+00:00
-- url     : https://prove2.me/submissions/b88fa916-c025-45c7-8486-2c096cb081f1

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The right-hand limit of the original source pre-jump path recovers the
original post-jump value, without a change of probability space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) :
    Function.rightLim
      (fun u : ℝ≥0 => Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
      t = X.X t ω := by
  have hright :
      Tendsto (fun u : ℝ≥0 => X.X u ω) (𝓝[>] t)
        (𝓝 (X.X t ω)) :=
    (X.rightCont ω t).mono_left
      (nhdsWithin_mono t Set.Ioi_subset_Ici_self)
  have hrightlim :
      Function.rightLim (fun u : ℝ≥0 => X.X u ω) t = X.X t ω :=
    (X.rightCont ω t).rightLim_eq
  have hlim :
      Tendsto (fun u : ℝ≥0 => X.X u ω) (𝓝[>] t)
        (𝓝 (Function.rightLim (fun u : ℝ≥0 => X.X u ω) t)) := by
    simpa only [hrightlim] using hright
  exact (rightLim_leftLim hlim).trans hrightlim
