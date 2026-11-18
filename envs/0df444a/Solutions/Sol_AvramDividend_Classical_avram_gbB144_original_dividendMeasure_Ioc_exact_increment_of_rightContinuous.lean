-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB144_original_dividendMeasure_Ioc_exact_increment_of_rightContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:01:46.074073+00:00
-- url     : https://prove2.me/submissions/3ada7c1b-f08c-4f2f-89ce-618875732b0c

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Original Stieltjes measure cell mass from right-continuous dividend paths. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (a b : ℝ)
    (hMono : Monotone (fun t : ℝ => D t.toNNReal ω))
    (hContA : ContinuousWithinAt
      (fun t : ℝ => D t.toNNReal ω) (Ici a) a)
    (hContB : ContinuousWithinAt
      (fun t : ℝ => D t.toNNReal ω) (Ici b) b) :
    dividendMeasure D ω (Ioc a b) =
      ENNReal.ofReal
        (D b.toNNReal ω - D a.toNNReal ω) := by
  unfold dividendMeasure
  rw [dif_pos hMono]
  rw [StieltjesFunction.measure_Ioc]
  simp only [Monotone.stieltjesFunction_eq]
  rw [hContA.rightLim_eq, hContB.rightLim_eq]
