-- Prove2me | solution 1 for AvramDividend.Classical.bv_dyadic_lintegral_active_cell_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:59:06.547477+00:00
-- url     : https://prove2.me/submissions/f5bba66a-c2cd-4d35-8ac4-aaeb22c8192e

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Finset
open scoped ENNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (E : ℕ → Set Ω) (N : ℕ)
    (hE : ∀ i : ℕ, i < N → MeasurableSet (E i)) :
    (∫⁻ ω, ∑ i ∈ range N, (E i).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P) =
      ∑ i ∈ range N, P (E i) := by
  rw [lintegral_finsetSum]
  · apply sum_congr rfl
    intro i hi
    exact lintegral_indicator_one (hE i (mem_range.mp hi))
  · intro i hi
    exact measurable_const.indicator (hE i (mem_range.mp hi))
