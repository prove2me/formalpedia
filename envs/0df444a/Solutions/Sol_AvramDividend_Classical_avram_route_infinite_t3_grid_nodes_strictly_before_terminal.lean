-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_infinite_t3_grid_nodes_strictly_before_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:24:59.817225+00:00
-- url     : https://prove2.me/submissions/53a2e3aa-1fac-48c1-ba3f-2f28e1209d2a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ n i, i ≤ n + 1 →
      u n i < (⟨T, le_of_lt hT⟩ : ℝ≥0) := by
  intro n i hi
  have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hiR : (i : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hi
  have hlt : (i : ℝ) < (n : ℝ) + 2 := by linarith
  have hmul : T * (i : ℝ) < T * ((n : ℝ) + 2) :=
    mul_lt_mul_of_pos_left hlt hT
  have hreal : (u n i : ℝ) < T := by
    rw [huniform]
    exact (div_lt_iff₀ hn).2 (by simpa [mul_comm] using hmul)
  exact_mod_cast hreal
