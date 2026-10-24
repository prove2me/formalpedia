-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_closed_horizon_lintegral_eq_stopped_add_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:18:42.610253+00:00
-- url     : https://prove2.me/submissions/ee15ea12-90b3-4c40-84e7-60dc8e460523

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_eq_inter_Iio_of_pos
import Theorems.Thm_AvramDividend_Classical_paymentTimes_closed_horizon_eq_truncated_union_terminal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The nonnegative Stieltjes integral over a closed positive horizon
    equals the strict stopped integral plus its terminal dividend atom. -/
theorem solution
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (σ : ℝ≥0∞) (T : ℝ) (hT : 0 < T) :
    (∫⁻ t in paymentTimes σ ∩ Set.Iic T, f t ∂μ) =
      (∫⁻ t in paymentTimes (min σ (ENNReal.ofReal T)), f t ∂μ) +
        (∫⁻ t in paymentTimes σ ∩ ({T} : Set ℝ), f t ∂μ) := by
  have hB : MeasurableSet (paymentTimes σ ∩ ({T} : Set ℝ)) := by
    by_cases hmem : T ∈ paymentTimes σ
    · have heq : paymentTimes σ ∩ ({T} : Set ℝ) = {T} := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
        constructor
        · exact fun ht => ht.2
        · intro ht
          subst t
          exact ⟨hmem, rfl⟩
      rw [heq]
      exact measurableSet_singleton T
    · have heq : paymentTimes σ ∩ ({T} : Set ℝ) = ∅ := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨ht, rfl⟩
        exact hmem ht
      rw [heq]
      exact MeasurableSet.empty
  have hdisj :
      Disjoint (paymentTimes (min σ (ENNReal.ofReal T)))
        (paymentTimes σ ∩ ({T} : Set ℝ)) := by
    rw [paymentTimes_min_ofReal_eq_inter_Iio_of_pos σ T hT]
    refine Set.disjoint_left.mpr ?_
    intro t htA htB
    have hless : t < T := htA.2
    have heq : t = T := htB.2
    subst t
    exact (lt_irrefl T) hless
  rw [paymentTimes_closed_horizon_eq_truncated_union_terminal
    σ T (le_of_lt hT)]
  exact lintegral_union hB hdisj
