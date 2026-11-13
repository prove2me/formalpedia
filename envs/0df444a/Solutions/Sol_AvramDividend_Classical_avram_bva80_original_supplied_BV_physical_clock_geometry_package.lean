-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva80_original_supplied_BV_physical_clock_geometry_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:23:36.208117+00:00
-- url     : https://prove2.me/submissions/3f6fb315-0340-49e5-b16b-0a2d5b1de981

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva77_original_uniform_source_terminal_clock_eq_strict_cash_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_bva78_original_supplied_uniform_endpoint_tendsto_real_horizon
import Theorems.Thm_AvramDividend_Classical_avram_bva79_original_supplied_uniform_physical_clock_strict_step
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    (∀ n : ℕ, u n 0 = 0) ∧
    (∀ n i : ℕ, u n i < u n (i + 1)) ∧
    (∀ n : ℕ, (u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2) ∧
      (u n (n + 1) : ℝ) < T) ∧
    Tendsto (fun n : ℕ => (u n (n + 1) : ℝ)) atTop (𝓝 T) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    have h0 : (u n 0 : ℝ) = 0 := by simpa using (huniform n 0)
    exact_mod_cast h0
  · exact avram_bva79_original_supplied_uniform_physical_clock_strict_step T hT u huniform
  · exact avram_bva77_original_uniform_source_terminal_clock_eq_strict_cash_cutoff T hT u huniform
  · exact avram_bva78_original_supplied_uniform_endpoint_tendsto_real_horizon T hT u huniform
