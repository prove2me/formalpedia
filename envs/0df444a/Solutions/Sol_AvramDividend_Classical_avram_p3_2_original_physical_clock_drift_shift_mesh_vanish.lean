-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_physical_clock_drift_shift_mesh_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:31:55.672201+00:00
-- url     : https://prove2.me/submissions/ff368117-899c-4987-949a-69885d59dd24

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Uniform shrinking physical clock cells force all physical BV drift
increments to vanish, regardless of the sign of the actual source drift. -/
theorem solution
    (b : ℝ) (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ)
    (hGrid : ∀ m i, i < n m → u m i ≤ u m (i + 1))
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
        (u m (i + 1) : ℝ) - (u m i : ℝ) < δ) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
        |((u m (i + 1) : ℝ) - (u m i : ℝ)) * b| < ε := by
  intro ε hε
  have hB : 0 < |b| + 1 := by linarith [abs_nonneg b]
  have hδ : 0 < ε / (|b| + 1) := div_pos hε hB
  filter_upwards [hMesh (ε / (|b| + 1)) hδ] with m hm
  intro i hi
  have hOrder : (u m i : ℝ) ≤ (u m (i + 1) : ℝ) :=
    NNReal.coe_le_coe.mpr (hGrid m i hi)
  have hNonneg :
      0 ≤ (u m (i + 1) : ℝ) - (u m i : ℝ) := sub_nonneg.mpr hOrder
  calc
    |((u m (i + 1) : ℝ) - (u m i : ℝ)) * b| =
      ((u m (i + 1) : ℝ) - (u m i : ℝ)) * |b| := by
        rw [abs_mul, abs_of_nonneg hNonneg]
    _ ≤ ((u m (i + 1) : ℝ) - (u m i : ℝ)) * (|b| + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hNonneg
    _ < (ε / (|b| + 1)) * (|b| + 1) :=
      mul_lt_mul_of_pos_right (hm i hi) hB
    _ = ε := by field_simp [ne_of_gt hB]
