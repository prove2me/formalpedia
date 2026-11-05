-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_assist_finite_weighted_mark_count_real_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:32:41.337539+00:00
-- url     : https://prove2.me/submissions/e7d446c2-323a-4320-bc34-61d2b7da8187

import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_count_restrict_map_test_lintegral
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal BigOperators

/-- Integrating a nonnegative real marked test against a restricted counting
pushforward is the ENNReal embedding of its actual finite supported jump sum. -/
theorem solution
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {β : Type*} [MeasurableSpace β]
    (J : Set α) (hJ : MeasurableSet J)
    (j : α → β) (hj : Measurable j)
    (g : β → ℝ) (hg : Measurable g)
    (hgnonneg : ∀ y : β, 0 ≤ g y)
    (F : Finset α)
    (hF : ∀ x : α, x ∈ F ↔ x ∈ J ∧ g (j x) ≠ 0) :
    (∫⁻ y, ENNReal.ofReal (g y) ∂((Measure.count.restrict J).map j)) =
      ENNReal.ofReal (∑ x ∈ F, g (j x)) := by
  classical
  have hmeas : Measurable (fun y : β => ENNReal.ofReal (g y)) :=
    ENNReal.measurable_ofReal.comp hg
  have hOutside (x : α) (hx : x ∉ F) :
      J.indicator (fun z => ENNReal.ofReal (g (j z))) x = 0 := by
    by_cases hxJ : x ∈ J
    · have hg0 : g (j x) = 0 := by
        by_contra hn
        exact hx ((hF x).2 ⟨hxJ, hn⟩)
      simp [Set.indicator_of_mem hxJ, hg0]
    · simp [Set.indicator_of_notMem hxJ]
  calc
    (∫⁻ y, ENNReal.ofReal (g y) ∂((Measure.count.restrict J).map j)) =
        ∑' x : α, J.indicator (fun z => ENNReal.ofReal (g (j z))) x :=
          avram_p2_a_zero_rate_count_restrict_map_test_lintegral
            J hJ j hj (fun y => ENNReal.ofReal (g y)) hmeas
    _ = ∑ x ∈ F, J.indicator (fun z => ENNReal.ofReal (g (j z))) x :=
          tsum_eq_sum hOutside
    _ = ∑ x ∈ F, ENNReal.ofReal (g (j x)) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [Set.indicator_of_mem ((hF x).1 hx).1]
    _ = ENNReal.ofReal (∑ x ∈ F, g (j x)) := by
      exact (ENNReal.ofReal_sum_of_nonneg
        (fun x hx => hgnonneg (j x))).symm
