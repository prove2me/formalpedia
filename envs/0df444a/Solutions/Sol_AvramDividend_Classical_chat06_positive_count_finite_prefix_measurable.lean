-- Prove2me | solution 1 for AvramDividend.Classical.chat06_positive_count_finite_prefix_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:37:42.737105+00:00
-- url     : https://prove2.me/submissions/b1a61950-1d0e-49e4-8413-2741bd8959a0

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Data.Fin.Basic

open MeasureTheory Set
namespace AvramChat06M
def padWaitPrefix (n : ℕ) (g : Fin (n + 2) → ℝ) (i : ℕ) : ℝ :=
  if h : i < n + 2 then g ⟨i, h⟩ else 0

def positiveCountPrefixEvent (n : ℕ) (t : ℝ) :
    Set (Fin (n + 2) → ℝ) :=
  {g | (∑ j ∈ Finset.range (n + 1), padWaitPrefix n g j) ≤ t ∧
    t < ∑ j ∈ Finset.range (n + 2), padWaitPrefix n g j}

theorem measurable_pad (n : ℕ) (i : ℕ) : Measurable fun g : Fin (n + 2) → ℝ => padWaitPrefix n g i := by
  unfold padWaitPrefix
  by_cases h : i < n + 2
  · simp only [h, dif_pos]; exact measurable_pi_apply _
  · simp only [h, dif_neg, not_false_eq_true]; exact measurable_const

end AvramChat06M

theorem solution (n : ℕ) (t : ℝ) :
    MeasurableSet (AvramChat06M.positiveCountPrefixEvent n t) := by
  unfold AvramChat06M.positiveCountPrefixEvent
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_le (Finset.measurable_sum _ fun j _ => AvramChat06M.measurable_pad n j)
      measurable_const
  · exact measurableSet_lt measurable_const
      (Finset.measurable_sum _ fun j _ => AvramChat06M.measurable_pad n j)
