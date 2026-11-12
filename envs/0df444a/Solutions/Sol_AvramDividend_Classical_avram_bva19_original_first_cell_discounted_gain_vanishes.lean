-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva19_original_first_cell_discounted_gain_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:46:25.749541+00:00
-- url     : https://prove2.me/submissions/43375cf4-c43e-4a38-b453-ee9ef31d7019

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (u : ℕ → ℕ → ℝ≥0) (hzero : ∀ n, u n 0 = 0)
    (hmesh : Tendsto (fun n => (u n 1 : ℝ)) atTop (𝓝 (0 : ℝ)))
    (U : ℝ≥0 → ℝ) (q : ℝ) (ψ : ℝ → ℝ) :
    Tendsto (fun n =>
      Real.exp (-(q * (u n 0 : ℝ))) * ψ (U (u n 0)) *
        ((u n 1 : ℝ) - (u n 0 : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
  have hrewrite :
      (fun n => Real.exp (-(q * (u n 0 : ℝ))) * ψ (U (u n 0)) *
        ((u n 1 : ℝ) - (u n 0 : ℝ))) =
      (fun n => ψ (U 0) * (u n 1 : ℝ)) := by
    funext n
    simp [hzero n]
  rw [hrewrite]
  simpa using hmesh.const_mul (ψ (U 0))
