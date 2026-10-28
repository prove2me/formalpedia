-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_discounted_partial_record_cell_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:23:39.48649+00:00
-- url     : https://prove2.me/submissions/69d65dca-e072-4c29-9640-8a471d73f1f4

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_bounds_record_increment

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
    (s t b h : ℝ) (hh : 0 ≤ h)
    (hs : runningSup X s.toNNReal ω = b)
    (ht : runningSup X t.toNNReal ω ≤ b + h) :
    (∫⁻ r, if r ∈ Set.Ioc s t then w r else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤
      w s * ENNReal.ofReal h := by
  have hinc :
      runningSup X t.toNNReal ω - runningSup X s.toNNReal ω ≤ h := by
    rw [hs]
    exact (sub_le_iff_le_add).2 (by simpa [add_comm] using ht)
  calc
    (∫⁻ r, if r ∈ Set.Ioc s t then w r else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤
        w s * ENNReal.ofReal
          (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω) :=
      (runningSup_discounted_interval_bounds_record_increment X ω w hw s t).2
    _ ≤ w s * ENNReal.ofReal h :=
      mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hinc) (by exact bot_le)
