-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_actual_canonical_grid_after_crossing_identically_stopped
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:39:33.061708+00:00
-- url     : https://prove2.me/submissions/f1910b57-e497-4b33-865d-e0b092f38dad

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_canonical_grid_monotone_zero_and_reaches_stop_v2
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (n j : ℕ) (t : ℝ≥0) (ht : t ≤ (n : ℝ≥0))
    (k : ℕ)
    (hk : min ((k : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t = t) :
    ∀ l : ℕ, k ≤ l →
      min ((l : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t = t := by
  let v : ℕ → ℝ≥0 := fun i =>
    min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
  have hmon : Monotone v :=
    (avram_jump6_B_actual_canonical_grid_monotone_zero_and_reaches_stop_v2
      n j t ht).1
  intro l hkl
  have hvk : v k = t := hk
  have hvl : v l ≤ t := min_le_right _ _
  have hle : t ≤ v l := by
    rw [← hvk]
    exact hmon hkl
  exact le_antisymm hvl hle
