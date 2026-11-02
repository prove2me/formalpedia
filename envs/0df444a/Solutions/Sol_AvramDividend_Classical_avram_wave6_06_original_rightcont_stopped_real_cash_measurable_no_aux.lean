-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_rightcont_stopped_real_cash_measurable_no_aux
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:02:48.817462+00:00
-- url     : https://prove2.me/submissions/db267f0b-5987-4fea-b204-eac776949a94

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_inclusive_random_clock_real_cash_aestronglyMeasurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Admissible original cash at its genuine right-continuous ruin-stopped clock
is a.e. strongly measurable, with all right-payment atoms included. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    AEStronglyMeasurable Cash P := by
  have hτReal : Measurable (fun ω : Ω => (τ ω : ℝ)) :=
    avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable τ hτ
  exact avram_wave6_06_original_inclusive_random_clock_real_cash_aestronglyMeasurable
    X x C D hD q τ hτReal Cash hCash
