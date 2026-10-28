-- Prove2me | solution 1 for AvramDividend.Classical.stopped_lintegral_initial_record_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T20:21:30.736787+00:00
-- url     : https://prove2.me/submissions/e917f87f-a0d6-4735-a848-ba20ee033c5f

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_through_first_positive_record

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (f : ℝ → ℝ≥0∞) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : (0 : ℝ) < X.X s ω), (s : ℝ≥0∞))) :
    (∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc (0 : ℝ) (u : ℝ) then f r else 0
      ∂(dividendMeasure (runningSup X) ω)) = 0 := by
  have h0 := runningSup_dividendMeasure_zero_through_first_positive_record X 0 le_rfl ω u hu
  have hae : ∀ᵐ r ∂(dividendMeasure (runningSup X) ω), r ∉ Set.Ioc (0 : ℝ) (u : ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp h0
  apply le_antisymm _ (zero_le)
  calc (∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc (0 : ℝ) (u : ℝ) then f r else 0
      ∂(dividendMeasure (runningSup X) ω))
      ≤ ∫⁻ r, (if r ∈ Set.Ioc (0 : ℝ) (u : ℝ) then f r else 0)
          ∂(dividendMeasure (runningSup X) ω) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ _r, 0 ∂(dividendMeasure (runningSup X) ω) := by
        apply lintegral_congr_ae
        filter_upwards [hae] with r hr
        simp [hr]
    _ = 0 := lintegral_zero
    _ ≤ 0 := le_rfl
