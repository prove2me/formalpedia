-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_killed_real_zero_cap_spatial_support_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:57:49.530528+00:00
-- url     : https://prove2.me/submissions/43fd4427-e7f0-4b69-ab45-abf6b81c9200

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_postpayment_reserve_joint_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Pre-ruin real Stieltjes support remains jointly Borel at the zero/cap and interior states. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x T : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (lower : ℕ → ℝ) (upper : ℕ → ℝ≥0∞) (n : ℕ) :
    MeasurableSet {p : ℝ × Ω |
      p.1 ∈ paymentTimes (ruinTime X x D p.2) ∧ p.1 ≤ T ∧
        (x + X.X p.1.toNNReal p.2 - rightLimit D p.1.toNNReal p.2 = 0 ∨ ENNReal.ofReal (x + X.X p.1.toNNReal p.2 - rightLimit D p.1.toNNReal p.2) = C)} ∧
    MeasurableSet {p : ℝ × Ω |
      p.1 ∈ paymentTimes (ruinTime X x D p.2) ∧ p.1 ≤ T ∧
        lower n < x + X.X p.1.toNNReal p.2 - rightLimit D p.1.toNNReal p.2 ∧ ENNReal.ofReal (x + X.X p.1.toNNReal p.2 - rightLimit D p.1.toNNReal p.2) < upper n} := by
  have hReal : Measurable (fun t : ℝ => t.toNNReal) :=
    measurable_real_toNNReal
  have hPair : Measurable (fun p : ℝ × Ω => (p.1.toNNReal, p.2)) :=
    (hReal.comp measurable_fst).prodMk measurable_snd
  let U : ℝ × Ω → ℝ :=
    fun p => x + X.X p.1.toNNReal p.2 - rightLimit D p.1.toNNReal p.2
  have hU : Measurable U :=
    (avram_wave8_20_original_postpayment_reserve_joint_measurable X x D hD).comp hPair
  have hE : Measurable (fun p => ENNReal.ofReal (U p)) := by
    exact ENNReal.measurable_ofReal.comp hU
  have hPayment : MeasurableSet
      {p : ℝ × Ω | p.1 ∈ paymentTimes (ruinTime X x D p.2)} :=
    paymentTimes_joint_measurable (ruinTime X x D)
      (ruinTime_measurable X x D hD)
  have hTime : MeasurableSet {p : ℝ × Ω | p.1 ≤ T} :=
    measurable_fst measurableSet_Iic
  have hZero : MeasurableSet (U ⁻¹' ({0} : Set ℝ)) :=
    hU (measurableSet_singleton 0)
  have hCap : MeasurableSet ((fun p => ENNReal.ofReal (U p)) ⁻¹' ({C} : Set ℝ≥0∞)) :=
    hE (measurableSet_singleton C)
  have hLow : MeasurableSet (U ⁻¹' Ioi (lower n)) :=
    hU measurableSet_Ioi
  have hUpper : MeasurableSet
      ((fun p => ENNReal.ofReal (U p)) ⁻¹' Iio (upper n)) :=
    hE measurableSet_Iio
  constructor
  · change MeasurableSet
      ({p : ℝ × Ω | p.1 ∈ paymentTimes (ruinTime X x D p.2)} ∩
        ({p : ℝ × Ω | p.1 ≤ T} ∩
          (U ⁻¹' ({0} : Set ℝ) ∪
            (fun p => ENNReal.ofReal (U p)) ⁻¹' ({C} : Set ℝ≥0∞))))
    exact hPayment.inter (hTime.inter (hZero.union hCap))
  · change MeasurableSet
      ({p : ℝ × Ω | p.1 ∈ paymentTimes (ruinTime X x D p.2)} ∩
        ({p : ℝ × Ω | p.1 ≤ T} ∩
          (U ⁻¹' Ioi (lower n) ∩
            (fun p => ENNReal.ofReal (U p)) ⁻¹' Iio (upper n))))
    exact hPayment.inter (hTime.inter (hLow.inter hUpper))
