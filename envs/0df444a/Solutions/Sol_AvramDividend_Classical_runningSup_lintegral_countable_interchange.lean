-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_lintegral_countable_interchange
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T21:01:12.604534+00:00
-- url     : https://prove2.me/submissions/dbaac147-53ee-44bb-acb1-ce1708ccdcbf

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_eq_stieltjes

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
    (w : ℝ → ℝ≥0∞) (hw : Measurable w)
    (u : ℕ → ℝ) :
    (∫⁻ r, (∑' i : ℕ,
        if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0)
        ∂(dividendMeasure (runningSup X) ω)) =
      (∑' i : ℕ,
        ∫⁻ r, if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0
          ∂(dividendMeasure (runningSup X) ω)) := by
  have hMeas (i : ℕ) :
      Measurable (fun r : ℝ =>
        if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0) := by
    exact Measurable.ite measurableSet_Ioc hw measurable_const
  exact MeasureTheory.lintegral_tsum (fun i => (hMeas i).aemeasurable)
