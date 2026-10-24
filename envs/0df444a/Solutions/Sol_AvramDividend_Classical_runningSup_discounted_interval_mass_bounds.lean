-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_discounted_interval_mass_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:47:05.81064+00:00
-- url     : https://prove2.me/submissions/edae2f36-8fa8-4fd1-9f55-36db9b3e9630

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_weight_bounds

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
    (w t * (dividendMeasure (runningSup X) ω) (Set.Ioc s t) ≤
      (∫⁻ r, if r ∈ Set.Ioc s t then w r else 0
         ∂(dividendMeasure (runningSup X) ω))) ∧
    ((∫⁻ r, if r ∈ Set.Ioc s t then w r else 0
         ∂(dividendMeasure (runningSup X) ω)) ≤
      w s * (dividendMeasure (runningSup X) ω) (Set.Ioc s t)) := by
  classical
  have hconst (c : ℝ≥0∞) :
      (∫⁻ r, if r ∈ Set.Ioc s t then c else 0
        ∂(dividendMeasure (runningSup X) ω)) =
        c * (dividendMeasure (runningSup X) ω) (Set.Ioc s t) := by
    simpa [Set.indicator] using
      (lintegral_indicator_const (μ := dividendMeasure (runningSup X) ω)
        measurableSet_Ioc c)
  obtain ⟨hlo, hhi⟩ :=
    AvramDividend.Classical.runningSup_discounted_interval_weight_bounds X ω w hw s t
  constructor
  · rw [← hconst (w t)]
    exact hlo
  · rw [← hconst (w s)]
    exact hhi
