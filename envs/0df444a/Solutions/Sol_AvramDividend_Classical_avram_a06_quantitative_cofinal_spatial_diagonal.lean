-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_quantitative_cofinal_spatial_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:22:05.577073+00:00
-- url     : https://prove2.me/submissions/4aab6ed8-8793-4e63-9595-b6d8ac8c9ee7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_monotone_diagonal_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped Topology
noncomputable section

theorem solution
    (E : ℕ → ℕ → ℝ) (hNonneg : ∀ n k, 0 ≤ E n k)
    (hRow : ∀ n, Tendsto (fun k => E n k) atTop (𝓝 (0 : ℝ))) :
    ∃ κ : ℕ → ℕ, StrictMono κ ∧ (∀ n, n ≤ κ n) ∧
      Tendsto (fun (n : ℕ) => ((n : ℝ) + 1) * E n (κ n))
        atTop (𝓝 (0 : ℝ))  := by
  let Q : ℕ → ℕ → ℝ := fun n k => ((n : ℝ) + 1) * E n k
  have hQnonneg : ∀ n k, 0 ≤ Q n k := by
    intro n k
    exact mul_nonneg (by positivity) (hNonneg n k)
  have hQrow : ∀ n, Tendsto (fun k => Q n k) atTop (𝓝 (0 : ℝ)) := by
    intro n
    simpa only [Q, mul_zero] using
      ((tendsto_const_nhds : Tendsto
          (fun _ : ℕ => ((n : ℝ) + 1)) atTop
          (𝓝 ((n : ℝ) + 1))).mul (hRow n))
  simpa only [Q] using
    (avram_bv_strict6_monotone_diagonal_mean Q hQnonneg hQrow)
