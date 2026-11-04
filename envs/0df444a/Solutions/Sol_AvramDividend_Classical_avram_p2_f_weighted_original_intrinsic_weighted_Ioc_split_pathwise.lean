-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_weighted_Ioc_split_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:27:04.129587+00:00
-- url     : https://prove2.me/submissions/3b9d1845-bd99-48ea-ba88-01b75fb9b5bd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_Ioc_split_pathwise

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every nonnegative past weight preserves exact pathwise splitting
of the original intrinsic marked rectangle count. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s u t : ℝ≥0) (hsu : s ≤ u) (hut : u ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (H : Ω → ℝ≥0∞) (ω : Ω) :
    H ω * ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc s t ×ˢ B) =
    H ω * ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc s u ×ˢ B) +
    H ω * ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc u t ×ˢ B) := by
  rw [avram_p2_f_weighted_original_intrinsic_Ioc_split_pathwise
    X s u t hsu hut B hB ω]
  exact mul_add _ _ _
