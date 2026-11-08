-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_original_stopped_bracket_measurable_of_progressive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:41:23.347898+00:00
-- url     : https://prove2.me/submissions/70fddc14-e693-47db-b812-9bc6abf835f9

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Progressive measurability and a genuine original stopping clock ensure
measurability of the stopped Gaussian quadratic-energy bracket. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0 × Ω → ℝ) (μtime : Measure ℝ≥0)
    (hProgressive : IsStronglyProgressive 𝓕.rightCont
      (fun t ω => ∫ s in Ioc (0 : ℝ≥0) t,
        (H (s, ω)) ^ 2 ∂μtime))
    (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ) :
    Measurable (stoppedValue
      (fun t ω => ∫ s in Ioc (0 : ℝ≥0) t,
        (H (s, ω)) ^ 2 ∂μtime) τ) := by
  exact (measurable_stoppedValue hProgressive hτ).mono
    hτ.measurableSpace_le le_rfl
