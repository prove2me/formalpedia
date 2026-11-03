-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_joint_measurable_postpayment_zero_cap_interior_supports
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:44:26.918978+00:00
-- url     : https://prove2.me/submissions/11435b6d-7dfd-4973-85f8-0ea777e53eaa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_postpayment_reserve_joint_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Original post-rightpayment state domains are jointly measurable, including their boundaries. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    MeasurableSet {p : ℝ≥0 × Ω |
      x + X.X p.1 p.2 - rightLimit D p.1 p.2 = 0 ∨
        ENNReal.ofReal (x + X.X p.1 p.2 - rightLimit D p.1 p.2) = C} ∧
    MeasurableSet {p : ℝ≥0 × Ω |
      0 < x + X.X p.1 p.2 - rightLimit D p.1 p.2 ∧
        ENNReal.ofReal (x + X.X p.1 p.2 - rightLimit D p.1 p.2) < C} := by
  let U : ℝ≥0 × Ω → ℝ :=
    fun p => x + X.X p.1 p.2 - rightLimit D p.1 p.2
  have hU : Measurable U :=
    avram_wave8_20_original_postpayment_reserve_joint_measurable X x D hD
  have hE : Measurable (fun p => ENNReal.ofReal (U p)) := by
    exact ENNReal.measurable_ofReal.comp hU
  have h0 : MeasurableSet (U ⁻¹' ({0} : Set ℝ)) :=
    hU (measurableSet_singleton 0)
  have hCap : MeasurableSet ((fun p => ENNReal.ofReal (U p)) ⁻¹' ({C} : Set ℝ≥0∞)) :=
    hE (measurableSet_singleton C)
  have hPos : MeasurableSet (U ⁻¹' Ioi (0 : ℝ)) :=
    hU measurableSet_Ioi
  have hLtCap : MeasurableSet
      ((fun p => ENNReal.ofReal (U p)) ⁻¹' Iio C) :=
    hE measurableSet_Iio
  constructor
  · change MeasurableSet
      (U ⁻¹' ({0} : Set ℝ) ∪
        (fun p => ENNReal.ofReal (U p)) ⁻¹' ({C} : Set ℝ≥0∞))
    exact h0.union hCap
  · change MeasurableSet
      (U ⁻¹' Ioi (0 : ℝ) ∩
        (fun p => ENNReal.ofReal (U p)) ⁻¹' Iio C)
    exact hPos.inter hLtCap
