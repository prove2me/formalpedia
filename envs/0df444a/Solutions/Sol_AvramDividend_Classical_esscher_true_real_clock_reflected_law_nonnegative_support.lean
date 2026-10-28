-- Prove2me | solution 1 for AvramDividend.Classical.esscher_true_real_clock_reflected_law_nonnegative_support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T20:45:17.390851+00:00
-- url     : https://prove2.me/submissions/fee36c27-0f86-4b8e-981e-28d1423ab7e0

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Q : Measure (Ω × ℝ)) :
    (Measure.map (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}) Q) (Iio (0 : ℝ)) = 0 := by
  set f := fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}
  have hpre : f ⁻¹' Iio (0 : ℝ) = ∅ := by
    ext z
    simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_lt, f]
    rw [neg_nonneg]
    by_cases hb : BddBelow {y : ℝ | ∃ s : ℝ≥0, s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}
    · exact csInf_le_of_le hb ⟨0, bot_le, (X.X_zero z.1).symm⟩ le_rfl
    · rw [Real.sInf_of_not_bddBelow hb]
  by_cases hm : AEMeasurable f Q
  · rw [Measure.map_apply_of_aemeasurable hm measurableSet_Iio, hpre, measure_empty]
  · rw [Measure.map_of_not_aemeasurable hm]; rfl
