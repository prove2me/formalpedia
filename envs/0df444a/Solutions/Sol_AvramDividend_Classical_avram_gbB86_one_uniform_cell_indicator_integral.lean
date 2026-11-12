-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB86_one_uniform_cell_indicator_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:13:08.151785+00:00
-- url     : https://prove2.me/submissions/e9748b7d-db1e-4ca9-af01-4c7c1b8201a2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB87_uniform_cell_open_horizon_measure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    (n N r : ℕ) (hn : 0 < n) (hN : 0 < N) (hr : r < N) (a : ℝ) :
    let δ : ℝ := (n : ℝ) / (N : ℝ)
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      (if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
        then a else 0) ∂volume) = δ * a := by
  intro δ
  have hμ := avram_gbB87_uniform_cell_open_horizon_measure
    n N r hn hN hr
  dsimp only at hμ
  calc
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      (if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
        then a else 0) ∂volume) =
      (∫ t in Ioo (0 : ℝ) (n : ℝ),
        (Ico ((r : ℝ) * δ) (((r + 1 : ℕ) : ℝ) * δ)).indicator
          (fun _ : ℝ => a) t ∂volume) := by
            apply setIntegral_congr_fun measurableSet_Ioo
            intro t ht
            simp only [Set.indicator, mem_Ico]
    _ = (∫ t in Ioo (0 : ℝ) (n : ℝ) ∩
        Ico ((r : ℝ) * δ) (((r + 1 : ℕ) : ℝ) * δ), a ∂volume) := by
          rw [setIntegral_indicator measurableSet_Ico]
    _ = δ * a := by
          rw [setIntegral_const]
          change (volume (Ioo (0 : ℝ) (n : ℝ) ∩
            Ico ((r : ℝ) * δ) (((r + 1 : ℕ) : ℝ) * δ))).toReal * a = δ * a
          rw [hμ]
