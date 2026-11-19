-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward65_fixed_double_integral_strongly_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T19:16:05.521204+00:00
-- url     : https://prove2.me/submissions/ac450246-1f98-4044-85bf-0801b47b29f5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
    {Ω α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν]
    (F : Ω → α → β → ℝ)
    (hF : StronglyMeasurable (fun p : β × (α × Ω) =>
      F p.2.2 p.2.1 p.1)) :
    StronglyMeasurable (fun ω : Ω =>
      ∫ t, ∫ z, F ω t z ∂ν ∂μ) := by
  have hInner : StronglyMeasurable (fun p : α × Ω =>
      ∫ z, F p.2 p.1 z ∂ν) :=
    StronglyMeasurable.integral_prod_left' hF
  exact StronglyMeasurable.integral_prod_left' hInner
