-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_17_original_finite_clock_negative_mark_value_kernel_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:56:45.680125+00:00
-- url     : https://prove2.me/submissions/e6fac3cf-fb10-4c4a-b13f-a4fd077002cd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_predictable_left_reserve_jointly_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The actual original negative-jump value increment is measurable over
physical time, the original sample space, and the source Lévy mark space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (T : ℝ≥0) :
    Measurable (fun p : (ℝ≥0 × Ω) × ℝ =>
      if p.1.1 ≤ T then
        w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
        w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)
      else 0) := by
  let U : ℝ≥0 × Ω → ℝ := fun p =>
    if p.1 ≤ T then
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1
    else 0
  have hU : Measurable U :=
    avram_wave7_17_original_finite_clock_predictable_left_reserve_jointly_measurable
      X x D hD T
  have hw : Measurable w :=
    (local_verification_candidate_borel_and_postPayment_adapted
      X x D hD w hw_cont hw_neg).1
  have hUlift : Measurable (fun p : (ℝ≥0 × Ω) × ℝ => U p.1) :=
    hU.comp measurable_fst
  have hz : Measurable (fun p : (ℝ≥0 × Ω) × ℝ => p.2) :=
    measurable_snd
  have hkernel : Measurable (fun p : (ℝ≥0 × Ω) × ℝ =>
      w (U p.1 + p.2) - w (U p.1)) :=
    (hw.comp (hUlift.add hz)).sub (hw.comp hUlift)
  have hclock : Measurable (fun p : (ℝ≥0 × Ω) × ℝ => p.1.1) :=
    measurable_fst.comp measurable_fst
  have htime : MeasurableSet
      {p : (ℝ≥0 × Ω) × ℝ | p.1.1 ≤ T} :=
    measurableSet_le hclock measurable_const
  have hfull : Measurable (fun p : (ℝ≥0 × Ω) × ℝ =>
      if p.1.1 ≤ T then w (U p.1 + p.2) - w (U p.1) else 0) :=
    Measurable.ite htime hkernel measurable_const
  convert hfull using 1
  funext p
  by_cases ht : p.1.1 ≤ T
  · simp [U, ht]
  · simp [U, ht]
