-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB145_original_cap_barrier_dividendMeasure_Ioc_exact_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:05:55.053957+00:00
-- url     : https://prove2.me/submissions/adc18172-d690-4102-99dd-2942cfa23676

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_monotone
import Theorems.Thm_AvramDividend_Classical_avram_gbB32_original_cap_barrier_full_continuity
import Theorems.Thm_AvramDividend_Classical_avram_gbB144_original_dividendMeasure_Ioc_exact_increment_of_rightContinuous
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Original barrier physical cash cell is the regulator increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ)
    (ω : Ω) (a b : ℝ) :
    dividendMeasure (barrierStrategy X c c) ω (Ioc a b) =
      ENNReal.ofReal
        (barrierStrategy X c c b.toNNReal ω -
          barrierStrategy X c c a.toNNReal ω) := by
  have hMono : Monotone
      (fun t : ℝ => barrierStrategy X c c t.toNNReal ω) := by
    intro s t hst
    exact (barrierStrategy_monotone X c ω) (Real.toNNReal_mono hst)
  have hCont : Continuous
      (fun t : ℝ => barrierStrategy X c c t.toNNReal ω) :=
    (avram_gbB32_original_cap_barrier_full_continuity X c ω).comp
      continuous_real_toNNReal
  exact avram_gbB144_original_dividendMeasure_Ioc_exact_increment_of_rightContinuous
    (barrierStrategy X c c) ω a b hMono
    (hCont.continuousAt.continuousWithinAt)
    (hCont.continuousAt.continuousWithinAt)
