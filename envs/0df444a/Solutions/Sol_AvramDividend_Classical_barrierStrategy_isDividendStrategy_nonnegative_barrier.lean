-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_isDividendStrategy_nonnegative_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T13:20:39.927668+00:00
-- url     : https://prove2.me/submissions/5e67408b-f839-4bcc-9f76-8608bc625265

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_monotone
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_left_continuous
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_capped_admissible_of_regular
import Theorems.Thm_AvramDividend_Classical_add_initial_excess_admissible_value
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_eq_thresholded_self_below_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_eq_add_initial_excess_above_barrier


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) :
    IsDividendStrategy 𝓕 (barrierStrategy X x a) := by
  by_cases hxa : x ≤ a
  · rw [AvramDividend.Classical.barrierStrategy_eq_thresholded_self_below_barrier
      X x a hx ha hxa]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ω
      have hzero : barrierStrategy X a a 0 ω = 0 := by
        simp [barrierStrategy]
      have hnonpos : x - a ≤ 0 := by
        linarith
      have hcalc : (0 : ℝ) - (a - x) = x - a := by
        ring
      change max 0 (barrierStrategy X a a 0 ω - (a - x)) = 0
      rw [hzero, hcalc, max_eq_left hnonpos]
    · intro ω s t hst
      have hmono :=
        AvramDividend.Classical.barrierStrategy_monotone X a ω hst
      exact max_le_max le_rfl (sub_le_sub_right hmono (a - x))
    · intro ω t
      exact continuousWithinAt_const.max
        ((AvramDividend.Classical.barrierStrategy_left_continuous X a ω t).sub
          continuousWithinAt_const)
    · intro t
      exact measurable_const.max
        (((AvramDividend.Classical.barrierStrategy_adapted X a) t).sub measurable_const)
  · have hax : a < x := lt_of_not_ge hxa
    have hbase :
        IsAdmissibleLe X a (ENNReal.ofReal a) (barrierStrategy X a a) :=
      AvramDividend.Classical.barrierStrategy_capped_admissible_of_regular
        X a ha
        (AvramDividend.Classical.barrierStrategy_left_continuous X a)
        (AvramDividend.Classical.barrierStrategy_right_continuous X a)
        (AvramDividend.Classical.barrierStrategy_adapted X a)
    have hadd :=
      (AvramDividend.Classical.add_initial_excess_admissible_value
        X 0 x a ha hax (barrierStrategy X a a) hbase).1
    rw [AvramDividend.Classical.barrierStrategy_eq_add_initial_excess_above_barrier
      X x a ha hax]
    exact hadd.1.1
