-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB88_finite_step_expectation_time_sum_interchange
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:20:29.515194+00:00
-- url     : https://prove2.me/submissions/15e0c705-e883-4489-afa6-9a8f2fd51078

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB89_expected_fixed_time_step_sum_linearity
import Theorems.Thm_AvramDividend_Classical_avram_gbB90_finite_time_step_sum_linearity
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
      (Finset.range N).sum (fun r =>
        ∫ t in Ioo (0 : ℝ) (n : ℝ),
          if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
          then (∫ ω, F r ω ∂P) else 0 ∂volume) := by
  intro δ
  let A : ℕ → ℝ := fun r => ∫ ω, F r ω ∂P
  have hFixed (t : ℝ) := avram_gbB89_expected_fixed_time_step_sum_linearity
    P N δ t F hF
  have hTime := avram_gbB90_finite_time_step_sum_linearity
    n N hn hN A
  dsimp only at hTime
  calc
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      (∫ ω, (Finset.range N).sum (fun r =>
        if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
        then F r ω else 0) ∂P) ∂volume) =
      (∫ t in Ioo (0 : ℝ) (n : ℝ),
        (Finset.range N).sum (fun r =>
          if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
          then A r else 0) ∂volume) := by
            apply setIntegral_congr_fun measurableSet_Ioo
            intro t ht
            simpa only [A] using hFixed t
    _ = (Finset.range N).sum (fun r =>
        ∫ t in Ioo (0 : ℝ) (n : ℝ),
          if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
          then (∫ ω, F r ω ∂P) else 0 ∂volume) := by
            simpa only [A] using hTime
