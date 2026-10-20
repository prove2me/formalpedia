-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_discounted_interval_bounds_rightLim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T18:19:34.052963+00:00
-- url     : https://prove2.me/submissions/a625bf6d-7b13-472f-93b8-5e5eb306787c

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_weight_bounds
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_rightLim
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (w : ℝ → ℝ≥0∞) (hw : Antitone w)
    (s t : ℝ) :
    (w t * ENNReal.ofReal
      (Function.rightLim (fun r : ℝ => runningSup X r.toNNReal ω) t -
       Function.rightLim (fun r : ℝ => runningSup X r.toNNReal ω) s) ≤
      ∫⁻ r, if r ∈ Set.Ioc s t then w r else 0
        ∂(dividendMeasure (runningSup X) ω)) ∧
    ((∫⁻ r, if r ∈ Set.Ioc s t then w r else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤
     w s * ENNReal.ofReal
      (Function.rightLim (fun r : ℝ => runningSup X r.toNNReal ω) t -
       Function.rightLim (fun r : ℝ => runningSup X r.toNNReal ω) s)) := by
  classical
  let μ := dividendMeasure (runningSup X) ω
  have hConst (c : ℝ≥0∞) :
      (∫⁻ r, if r ∈ Set.Ioc s t then c else 0 ∂μ) =
        c * μ (Set.Ioc s t) := by
    simpa only [Set.indicator] using
      (lintegral_indicator_const (μ := μ)
        (s := Set.Ioc s t) measurableSet_Ioc c)
  have hMass :
      μ (Set.Ioc s t) =
        ENNReal.ofReal
          (Function.rightLim
            (fun r : ℝ => runningSup X r.toNNReal ω) t -
           Function.rightLim
            (fun r : ℝ => runningSup X r.toNNReal ω) s) :=
    runningSup_dividendMeasure_Ioc_rightLim X ω s t
  obtain ⟨hLo, hHi⟩ :=
    runningSup_discounted_interval_weight_bounds X ω w hw s t
  constructor
  · calc
      w t * ENNReal.ofReal
        (Function.rightLim
            (fun r : ℝ => runningSup X r.toNNReal ω) t -
         Function.rightLim
            (fun r : ℝ => runningSup X r.toNNReal ω) s) =
        (∫⁻ r, if r ∈ Set.Ioc s t then w t else 0 ∂μ) := by
          rw [hConst, hMass]
      _ ≤ (∫⁻ r, if r ∈ Set.Ioc s t then w r else 0 ∂μ) := hLo
  · calc
      (∫⁻ r, if r ∈ Set.Ioc s t then w r else 0 ∂μ) ≤
        (∫⁻ r, if r ∈ Set.Ioc s t then w s else 0 ∂μ) := hHi
      _ = w s * ENNReal.ofReal
        (Function.rightLim
            (fun r : ℝ => runningSup X r.toNNReal ω) t -
         Function.rightLim
            (fun r : ℝ => runningSup X r.toNNReal ω) s) := by
          rw [hConst, hMass]
