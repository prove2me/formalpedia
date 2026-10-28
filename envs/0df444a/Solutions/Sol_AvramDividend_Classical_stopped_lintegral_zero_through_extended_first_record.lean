-- Prove2me | solution 1 for AvramDividend.Classical.stopped_lintegral_zero_through_extended_first_record
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:33:28.121384+00:00
-- url     : https://prove2.me/submissions/16ab76bf-0085-468a-a234-8a1f49dbc569

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_up_to_extended_first_positive_record

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (f : ℝ → ℝ≥0∞) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) ≤
      (⨅ (r : ℝ≥0) (_ : (0 : ℝ) < X.X r ω), (r : ℝ≥0∞))) :
    (∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc (0 : ℝ) (t : ℝ) then f r else 0
      ∂(dividendMeasure (runningSup X) ω)) = 0 := by
  have hzero :=
    runningSup_dividendMeasure_zero_up_to_extended_first_positive_record
      X ω t ht
  have hae : ∀ᵐ r ∂(dividendMeasure (runningSup X) ω),
      r ∉ Set.Ioc (0 : ℝ) (t : ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp hzero
  apply le_antisymm _ zero_le
  calc
    (∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc (0 : ℝ) (t : ℝ) then f r else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤
        ∫⁻ r, (if r ∈ Set.Ioc (0 : ℝ) (t : ℝ) then f r else 0)
          ∂(dividendMeasure (runningSup X) ω) :=
            setLIntegral_le_lintegral _ _
    _ = ∫⁻ _r, 0 ∂(dividendMeasure (runningSup X) ω) := by
      apply lintegral_congr_ae
      filter_upwards [hae] with r hr
      simp [hr]
    _ = 0 := lintegral_zero
    _ ≤ 0 := le_rfl
