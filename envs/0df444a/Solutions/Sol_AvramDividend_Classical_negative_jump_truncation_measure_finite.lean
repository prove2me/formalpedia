-- Prove2me | solution 1 for AvramDividend.Classical.negative_jump_truncation_measure_finite
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:36:37.340747+00:00
-- url     : https://prove2.me/submissions/d702aab8-5869-4aba-a995-f5a1a0ac81e1

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- The Lévy small-jump integrability bound makes every negative truncation finite. -/
theorem solution
    (ν : Measure ℝ)
    (hν : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν < ⊤)
    (δ : ℝ) (hδ : 0 < δ) :
    ν (Iic (-δ)) < ⊤ := by 
  have hc : 0 < min 1 (δ ^ 2) := lt_min one_pos (by positivity)
  have h : ENNReal.ofReal (min 1 (δ ^ 2)) * ν (Iic (-δ)) ≤ ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν := by
    rw [← lintegral_indicator_const measurableSet_Iic]
    apply lintegral_mono
    intro y
    by_cases hy : y ∈ Iic (-δ)
    · rw [Set.indicator_of_mem hy]
      apply ENNReal.ofReal_le_ofReal
      have : δ ^ 2 ≤ y ^ 2 := by
        have := Set.mem_Iic.1 hy
        nlinarith
      exact min_le_min le_rfl this
    · rw [Set.indicator_of_notMem hy]; exact bot_le
  exact ENNReal.lt_top_of_mul_ne_top_right (ne_top_of_le_ne_top hν.ne h)
    (ENNReal.ofReal_pos.2 hc).ne'
