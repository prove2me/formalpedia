-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_real_stopped_paymentTimes_subset_closed_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:07:02.251443+00:00
-- url     : https://prove2.me/submissions/75ed0894-487f-432c-b70e-fa1eca871309

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_eq_inter_Iio_of_pos
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (τ : ℝ≥0∞) (T : ℝ) (hT : 0 ≤ T) :
    paymentTimes (min τ (ENNReal.ofReal T)) ⊆ Set.Iic T := by
  by_cases hz : T = 0
  · subst T
    rw [ENNReal.ofReal_zero, paymentTimes_min_zero_eq_singleton_zero τ]
    intro t ht
    have ht0 : t = 0 := by simpa only [Set.mem_singleton_iff] using ht
    simpa [ht0]
  · have hp : 0 < T := lt_of_le_of_ne hT (Ne.symm hz)
    rw [paymentTimes_min_ofReal_eq_inter_Iio_of_pos τ T hp]
    intro t ht
    have hlt : t < T := by simpa only [Set.mem_Iio] using ht.2
    change t ≤ T
    exact le_of_lt hlt
