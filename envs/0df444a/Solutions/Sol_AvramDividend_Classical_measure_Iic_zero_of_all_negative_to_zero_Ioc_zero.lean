-- Prove2me | solution 1 for AvramDividend.Classical.measure_Iic_zero_of_all_negative_to_zero_Ioc_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:00:21.923096+00:00
-- url     : https://prove2.me/submissions/f1b13acc-7034-474b-aed9-409a6ec5fe83

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.Linarith

open MeasureTheory Set
open scoped ENNReal
theorem solution
    (μ : Measure ℝ)
    (hwindow : ∀ s : ℝ, s < 0 →
      μ (Set.Ioc s (0 : ℝ)) = 0) :
    μ (Set.Iic (0 : ℝ)) = 0 := by
  refine measure_mono_null (fun x (hx : x ≤ 0) => ?_)
    (measure_iUnion_null fun n : ℕ => hwindow (-(n : ℝ) - 1) (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]))
  obtain ⟨n, hn⟩ := exists_nat_gt (-x)
  exact Set.mem_iUnion.2 ⟨n, by constructor <;> linarith⟩
