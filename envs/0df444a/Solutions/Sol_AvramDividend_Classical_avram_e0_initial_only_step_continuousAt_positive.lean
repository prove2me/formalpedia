-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_initial_only_step_continuousAt_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:18:41.720369+00:00
-- url     : https://prove2.me/submissions/c9f850b3-8349-4a74-90f8-c50720bceced

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.Continuous
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- An initial-only step is constant in a neighbourhood of every positive time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (K : Ω → ℝ) (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    ContinuousAt (fun s : ℝ≥0 => if s = 0 then (0 : ℝ) else K ω) t := by
  have hevent :
      (fun s : ℝ≥0 => if s = 0 then (0 : ℝ) else K ω) =ᶠ[nhds t]
        (fun _ : ℝ≥0 => K ω) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    change 0 < s at hs
    simp [ne_of_gt hs]
  exact (ContinuousAt.congr_of_eventuallyEq continuousAt_const hevent)
