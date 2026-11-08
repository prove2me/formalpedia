-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_initial_only_dividend_leftcont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:06:32.575702+00:00
-- url     : https://prove2.me/submissions/08f6f0ab-2955-4255-97de-5d6fa61fb015

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.ContinuousOn
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A single initial payment has no discontinuity when approached from the left. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (K : Ω → ℝ) (ω : Ω) :
    ∀ t : ℝ≥0, ContinuousWithinAt
      (fun s : ℝ≥0 => if s = 0 then (0 : ℝ) else K ω) (Iic t) t := by
  intro t
  by_cases ht : t = 0
  · subst t
    have hset : (Iic (0 : ℝ≥0)) = {(0 : ℝ≥0)} := by
      ext s
      simp only [mem_Iic, mem_singleton_iff]
      constructor
      · intro hs
        exact le_antisymm hs (show 0 ≤ s from zero_le)
      · intro hs
        subst s
        exact le_refl 0
    rw [hset]
    exact continuousWithinAt_singleton
  · have hpos : 0 < t := lt_of_le_of_ne (show 0 ≤ t from zero_le) (Ne.symm ht)
    have hevent :
        (fun s : ℝ≥0 => if s = 0 then (0 : ℝ) else K ω) =ᶠ[nhds t]
          (fun _ : ℝ≥0 => K ω) := by
      filter_upwards [isOpen_Ioi.mem_nhds hpos] with s hs
      change 0 < s at hs
      simp [ne_of_gt hs]
    exact (ContinuousAt.congr_of_eventuallyEq continuousAt_const hevent).continuousWithinAt
