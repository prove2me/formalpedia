-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_discounted_interval_bounds_record_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:23:56.399993+00:00
-- url     : https://prove2.me/submissions/29e999c6-d1f2-4b7a-ab85-57b11617e165

import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_bounds_rightLim
import Theorems.Thm_AvramDividend_Classical_runningSup_realTime_rightLim_eq
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (w : ℝ → ℝ≥0∞) (hw : Antitone w)
    (s t : ℝ) :
    (w t * ENNReal.ofReal
       (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω) ≤
       ∫⁻ r, if r ∈ Set.Ioc s t then w r else 0
         ∂(dividendMeasure (runningSup X) ω)) ∧
    ((∫⁻ r, if r ∈ Set.Ioc s t then w r else 0
         ∂(dividendMeasure (runningSup X) ω)) ≤
      w s * ENNReal.ofReal
       (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω)) := by
  simpa only [runningSup_realTime_rightLim_eq X ω s,
              runningSup_realTime_rightLim_eq X ω t] using
    (runningSup_discounted_interval_bounds_rightLim X ω w hw s t)
