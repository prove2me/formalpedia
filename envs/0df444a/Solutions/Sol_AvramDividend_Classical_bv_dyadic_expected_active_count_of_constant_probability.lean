-- Prove2me | solution 1 for AvramDividend.Classical.bv_dyadic_expected_active_count_of_constant_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:04:41.710069+00:00
-- url     : https://prove2.me/submissions/d97644e4-0efb-4f1d-b9cd-3b311314cff9

import Theorems.Thm_AvramDividend_Classical_bv_dyadic_lintegral_active_cell_count
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Finset
open scoped ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (E : ℕ → Set Ω) (N : ℕ) (p : ℝ≥0∞)
    (hE : ∀ i : ℕ, i < N → MeasurableSet (E i))
    (hp : ∀ i : ℕ, i < N → P (E i) = p) :
    (∫⁻ ω, ∑ i ∈ Finset.range N,
      (E i).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P) =
      (N : ℝ≥0∞) * p := by
  rw [bv_dyadic_lintegral_active_cell_count P E N hE]
  calc
    ∑ i ∈ Finset.range N, P (E i) = ∑ i ∈ Finset.range N, p := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hp i (Finset.mem_range.mp hi)
    _ = (N : ℝ≥0∞) * p := by simp
