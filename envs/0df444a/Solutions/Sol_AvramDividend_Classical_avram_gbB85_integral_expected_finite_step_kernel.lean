-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB85_integral_expected_finite_step_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:14:51.085062+00:00
-- url     : https://prove2.me/submissions/46fc445c-4363-4c0d-be09-328a343b9683

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB86_one_uniform_cell_indicator_integral
import Theorems.Thm_AvramDividend_Classical_avram_gbB88_finite_step_expectation_time_sum_interchange
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (n N : ℕ) (hn : 0 < n) (hN : 0 < N)
    (F : ℕ → Ω → ℝ) (hF : ∀ r, Integrable (F r) P) :
    let δ : ℝ := (n : ℝ) / (N : ℝ)
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      (∫ ω, (Finset.range N).sum (fun r =>
        if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
        then F r ω else 0) ∂P) ∂volume) =
      δ * (Finset.range N).sum (fun r => ∫ ω, F r ω ∂P) := by
  intro δ
  have hSwap := avram_gbB88_finite_step_expectation_time_sum_interchange
    P n N hn hN F hF
  dsimp only at hSwap
  calc
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      (∫ ω, (Finset.range N).sum (fun r =>
        if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
        then F r ω else 0) ∂P) ∂volume) =
      (Finset.range N).sum (fun r =>
        ∫ t in Ioo (0 : ℝ) (n : ℝ),
          if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
          then (∫ ω, F r ω ∂P) else 0 ∂volume) := hSwap
    _ = (Finset.range N).sum (fun r => δ * (∫ ω, F r ω ∂P)) := by
          apply Finset.sum_congr rfl
          intro r hr
          simpa only [δ] using
            avram_gbB86_one_uniform_cell_indicator_integral
              n N r hn hN (Finset.mem_range.mp hr) (∫ ω, F r ω ∂P)
    _ = δ * (Finset.range N).sum (fun r => ∫ ω, F r ω ∂P) := by
          rw [Finset.mul_sum]
