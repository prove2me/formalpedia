-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_17_original_finite_clock_generator_mark_integrand_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:01:39.81383+00:00
-- url     : https://prove2.me/submissions/c295a31e-ad1a-41e8-bf84-65c4ffd9887c

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

/-- The original compensated negative-source-mark generator kernel is
jointly measurable on the finite original physical clock and mark space. -/
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
        SpectrallyNegativeLevy.generatorIntegrand w
          (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1) p.2
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
  have hderiv : Measurable (deriv w) := measurable_deriv w
  have hUlift : Measurable (fun p : (ℝ≥0 × Ω) × ℝ => U p.1) :=
    hU.comp measurable_fst
  have hz : Measurable (fun p : (ℝ≥0 × Ω) × ℝ => p.2) :=
    measurable_snd
  have hind : Measurable (fun p : (ℝ≥0 × Ω) × ℝ =>
      (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) p.2) :=
    (measurable_const.indicator measurableSet_Ioo).comp measurable_snd
  have hkernel : Measurable (fun p : (ℝ≥0 × Ω) × ℝ =>
      w (U p.1 + p.2) - w (U p.1) -
        deriv w (U p.1) * p.2 *
          (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) p.2) :=
    ((hw.comp (hUlift.add hz)).sub (hw.comp hUlift)).sub
      (((hderiv.comp hUlift).mul hz).mul hind)
  have hclock : Measurable (fun p : (ℝ≥0 × Ω) × ℝ => p.1.1) :=
    measurable_fst.comp measurable_fst
  have htime : MeasurableSet
      {p : (ℝ≥0 × Ω) × ℝ | p.1.1 ≤ T} :=
    measurableSet_le hclock measurable_const
  have hfull : Measurable (fun p : (ℝ≥0 × Ω) × ℝ =>
      if p.1.1 ≤ T then
        w (U p.1 + p.2) - w (U p.1) -
          deriv w (U p.1) * p.2 *
            (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) p.2
      else 0) :=
    Measurable.ite htime hkernel measurable_const
  convert hfull using 1
  funext p
  by_cases ht : p.1.1 ≤ T
  · simp [U, SpectrallyNegativeLevy.generatorIntegrand, ht]
  · simp [U, ht]
