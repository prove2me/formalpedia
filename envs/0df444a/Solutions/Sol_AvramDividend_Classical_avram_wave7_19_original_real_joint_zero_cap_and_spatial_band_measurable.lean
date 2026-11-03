-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_real_joint_zero_cap_and_spatial_band_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:57:44.299053+00:00
-- url     : https://prove2.me/submissions/f75d3ab6-cd2c-4540-979a-f2f9d87c1bee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_postpayment_reserve_joint_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- The real-time source Stieltjes spatial boundary and every interior band are Borel jointly. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    MeasurableSet {p : ℝ × Ω |
      0 ≤ p.1 ∧ (x + X.X p.1.toNNReal p.2 - rightLimit D p.1.toNNReal p.2 = 0 ∨
        ENNReal.ofReal (x + X.X p.1.toNNReal p.2 - rightLimit D p.1.toNNReal p.2) = C)} ∧
    (∀ (lower : ℕ → ℝ) (upper : ℕ → ℝ≥0∞) (n : ℕ),
      MeasurableSet {p : ℝ × Ω |
        0 ≤ p.1 ∧ lower n < x + X.X p.1.toNNReal p.2 - rightLimit D p.1.toNNReal p.2 ∧
          ENNReal.ofReal (x + X.X p.1.toNNReal p.2 - rightLimit D p.1.toNNReal p.2) < upper n}) := by
  have htReal : Measurable (fun t : ℝ => t.toNNReal) :=
    measurable_real_toNNReal
  have hPair : Measurable (fun p : ℝ × Ω => (p.1.toNNReal, p.2)) :=
    (htReal.comp measurable_fst).prodMk measurable_snd
  let U : ℝ × Ω → ℝ :=
    fun p => x + X.X p.1.toNNReal p.2 - rightLimit D p.1.toNNReal p.2
  have hU : Measurable U :=
    (avram_wave8_20_original_postpayment_reserve_joint_measurable X x D hD).comp hPair
  have hE : Measurable (fun p => ENNReal.ofReal (U p)) := by
    exact ENNReal.measurable_ofReal.comp hU
  have hTime : MeasurableSet {p : ℝ × Ω | 0 ≤ p.1} :=
    measurable_fst measurableSet_Ici
  have h0 : MeasurableSet (U ⁻¹' ({0} : Set ℝ)) :=
    hU (measurableSet_singleton 0)
  have hCap : MeasurableSet ((fun p => ENNReal.ofReal (U p)) ⁻¹' ({C} : Set ℝ≥0∞)) :=
    hE (measurableSet_singleton C)
  constructor
  · change MeasurableSet
      ({p : ℝ × Ω | 0 ≤ p.1} ∩
        (U ⁻¹' ({0} : Set ℝ) ∪
          (fun p => ENNReal.ofReal (U p)) ⁻¹' ({C} : Set ℝ≥0∞)))
    exact hTime.inter (h0.union hCap)
  · intro lower upper n
    have hLow : MeasurableSet (U ⁻¹' Ioi (lower n)) :=
      hU measurableSet_Ioi
    have hUp : MeasurableSet
        ((fun p => ENNReal.ofReal (U p)) ⁻¹' Iio (upper n)) :=
      hE measurableSet_Iio
    change MeasurableSet
      ({p : ℝ × Ω | 0 ≤ p.1} ∩
        (U ⁻¹' Ioi (lower n) ∩
          (fun p => ENNReal.ofReal (U p)) ⁻¹' Iio (upper n)))
    exact hTime.inter (hLow.inter hUp)
