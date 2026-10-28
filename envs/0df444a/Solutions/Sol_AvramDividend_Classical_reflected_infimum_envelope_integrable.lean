-- Prove2me | solution 1 for AvramDividend.Classical.reflected_infimum_envelope_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:56:38.313086+00:00
-- url     : https://prove2.me/submissions/5100d0db-bfa5-4f3f-a137-f6b375ca5574

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

/-- The reflected-infimum exponential envelope is integrable at every finite horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    Integrable (fun ω : Ω =>
      Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / θ) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hmax : Measurable (fun ω : Ω =>
      max (0 : ℝ) (-sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ t ∧ y = X.X s ω})) :=
    measurable_const.max (levy_running_infimum_measurable X t)
  have hmeas : Measurable (fun ω : Ω =>
      Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / θ) :=
    (Real.measurable_exp.comp (hmax.const_mul (-θ))).div_const θ
  apply Integrable.of_bound hmeas.aestronglyMeasurable (1 / θ)
  filter_upwards [] with ω
  have hn : 0 ≤ max (0 : ℝ)
      (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω}) :=
    le_max_left _ _
  have hmul : -θ * max (0 : ℝ)
      (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω}) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ.le) hn
  have hexp : Real.exp (-θ * max (0 : ℝ)
      (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) ≤ 1 :=
    Real.exp_le_one_iff.mpr hmul
  have hnonneg : 0 ≤ Real.exp (-θ * max (0 : ℝ)
      (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / θ :=
    div_nonneg (Real.exp_nonneg _) hθ.le
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact div_le_div_of_nonneg_right hexp hθ.le
