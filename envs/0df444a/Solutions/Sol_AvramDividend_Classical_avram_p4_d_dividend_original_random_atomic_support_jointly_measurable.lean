-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_random_atomic_support_jointly_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T20:34:26.291143+00:00
-- url     : https://prove2.me/submissions/8392cce3-2b1e-40cc-a8b9-c92855ca5cc5

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_singleton_indicator_kernel_lintegral_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The positive singleton masses of the actual original dividend Stieltjes
measure form a jointly measurable graph in the path and payment time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    MeasurableSet {p : Ω × ℝ | 0 < dividendMeasure D p.1 {p.2}} := by
  have hlin :=
    avram_p4_d_dividend_original_random_singleton_indicator_kernel_lintegral_measurable
      D hD
  have hpoint (p : Ω × ℝ) :
      (∫⁻ s : ℝ, (if s = p.2 then (1 : ℝ≥0∞) else 0)
        ∂dividendMeasure D p.1) = dividendMeasure D p.1 {p.2} := by
    calc
      _ = ∫⁻ s : ℝ, ({p.2} : Set ℝ).indicator
          (fun _ => (1 : ℝ≥0∞)) s ∂dividendMeasure D p.1 := by
            apply lintegral_congr
            intro s
            by_cases hs : s = p.2 <;> simp [Set.indicator, hs]
      _ = _ := lintegral_indicator_fun_one (measurableSet_singleton p.2)
  have hmass : Measurable (fun p : Ω × ℝ =>
      dividendMeasure D p.1 {p.2}) := by
    convert hlin using 1
    funext p
    exact (hpoint p).symm
  exact hmass measurableSet_Ioi
