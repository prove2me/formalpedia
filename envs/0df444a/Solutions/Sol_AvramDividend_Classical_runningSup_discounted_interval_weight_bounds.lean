-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_discounted_interval_weight_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T13:32:57.826126+00:00
-- url     : https://prove2.me/submissions/43a28db2-c1ab-4a60-b1bd-8ab157863f4d

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection

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
    ((∫⁻ r, if r ∈ Set.Ioc s t then w t else 0
         ∂(dividendMeasure (runningSup X) ω)) ≤
     (∫⁻ r, if r ∈ Set.Ioc s t then w r else 0
         ∂(dividendMeasure (runningSup X) ω))) ∧
    ((∫⁻ r, if r ∈ Set.Ioc s t then w r else 0
         ∂(dividendMeasure (runningSup X) ω)) ≤
     (∫⁻ r, if r ∈ Set.Ioc s t then w s else 0
         ∂(dividendMeasure (runningSup X) ω))) := by
  classical
  constructor
  · apply lintegral_mono
    intro r
    by_cases hr : r ∈ Set.Ioc s t
    · simpa only [if_pos hr] using (hw hr.2)
    · simpa only [if_neg hr] using
        (le_refl (0 : ℝ≥0∞))
  · apply lintegral_mono
    intro r
    by_cases hr : r ∈ Set.Ioc s t
    · simpa only [if_pos hr] using (hw hr.1.le)
    · simpa only [if_neg hr] using
        (le_refl (0 : ℝ≥0∞))
