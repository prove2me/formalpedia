-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_C1_zero_discount_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:11:01.955707+00:00
-- url     : https://prove2.me/submissions/061f5def-b444-4ef1-ba0a-6a307557171b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.NormNum
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_discount_scale_exists_from_zero
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_excursion_integrated_scale_representation
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_ordered_integrated_excursion_tail
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_C1_zero_iff_positive_discount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Reduce zero-discount C1 regularity to the positive-discount excursion representation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (hW : IsScaleFunction X 0 W)
    (hnbv : ¬ X.BoundedVariation) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by
  have hq : (0 : ℝ) < 1 := by norm_num
  obtain ⟨Wq, hWq⟩ :=
    unbounded_positive_discount_scale_exists_from_zero X hnbv W hW 1 hq
  obtain ⟨φ, μ, hφ, hnull, hfinite, htail, hrep⟩ :=
    unbounded_esscher_excursion_integrated_scale_representation
      X 1 hq Wq hWq hnbv
  have hcontinuous : ContinuousOn (fun t : ℝ => φ + μ.real (Ici t))
      (Ioi (0 : ℝ)) :=
    continuousOn_const.add htail
  have hqC1 : ContDiffOn ℝ 1 Wq (Ioi (0 : ℝ)) :=
    contDiffOn_one_of_ordered_integrated_excursion_tail
      (fun t : ℝ => φ + μ.real (Ici t)) Wq 1 hq hcontinuous hrep
  exact (unbounded_scale_C1_zero_iff_positive_discount
    X hnbv W hW 1 hq Wq hWq).2 hqC1
