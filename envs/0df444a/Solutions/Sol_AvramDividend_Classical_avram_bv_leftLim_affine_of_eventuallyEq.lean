-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_leftLim_affine_of_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:00:52.685645+00:00
-- url     : https://prove2.me/submissions/956d8e9b-8238-46e5-9949-259e359d815b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical Filter Topology AvramDividend.Classical
open scoped Topology NNReal ENNReal
noncomputable section

theorem solution
    (f : ℝ≥0 → ℝ) (t : ℝ≥0) (a b : ℝ)
    [Filter.NeBot (𝓝[<] t)]
    (hEvent : f =ᶠ[𝓝[<] t] (fun s : ℝ≥0 => a + b * (s : ℝ))) :
    Function.leftLim f t = a + b * (t : ℝ) := by
  apply leftLim_eq_of_tendsto
  have hCont : Continuous (fun s : ℝ≥0 => a + b * (s : ℝ)) :=
    continuous_const.add (continuous_const.mul continuous_subtype_val)
  have hTend : Tendsto (fun s : ℝ≥0 => a + b * (s : ℝ))
      (𝓝[<] t) (𝓝 (a + b * (t : ℝ))) :=
    hCont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact hTend.congr' hEvent.symm
