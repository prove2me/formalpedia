-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_restrictedMass_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T08:26:04.940487+00:00
-- url     : https://prove2.me/submissions/05ef0806-3afe-4cd9-9d95-f5b10d4522a9

import Mathlib.MeasureTheory.Measure.GiryMonad
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_restrict_Ioc_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ) :
    Measurable (fun ω : Ω =>
      ((dividendMeasure (runningSup X) ω).restrict (Set.Ioc s t)) Set.univ) := by
  exact (Measure.measurable_coe MeasurableSet.univ).comp
    (runningSup_dividendMeasure_restrict_Ioc_measurable X s t)
