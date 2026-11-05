-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_physical_drift_grid_total_variation_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:42:55.724396+00:00
-- url     : https://prove2.me/submissions/913c6463-4dd8-4d68-977e-f12ca912bf88

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Physical monotone clock variation telescopes for every signed drift. -/
theorem solution
    (b : ℝ) (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i, i < n → u i ≤ u (i + 1)) :
    (∑ i ∈ Finset.range n,
      |((u (i + 1) : ℝ) - (u i : ℝ)) * b|) =
      ((u n : ℝ) - (u 0 : ℝ)) * |b| := by
  calc
    _ = ∑ i ∈ Finset.range n,
        ((u (i + 1) : ℝ) - (u i : ℝ)) * |b| := by
      apply Finset.sum_congr rfl
      intro i hi
      have hOrder : (u i : ℝ) ≤ (u (i + 1) : ℝ) :=
        NNReal.coe_le_coe.mpr (hGrid i (Finset.mem_range.mp hi))
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hOrder)]
    _ = (∑ i ∈ Finset.range n,
        ((u (i + 1) : ℝ) - (u i : ℝ))) * |b| := by
      rw [Finset.sum_mul]
    _ = ((u n : ℝ) - (u 0 : ℝ)) * |b| := by
      have hTel (k : ℕ) :
          (∑ i ∈ Finset.range k,
            ((u (i + 1) : ℝ) - (u i : ℝ))) =
          (u k : ℝ) - (u 0 : ℝ) := by
        induction k with
        | zero => simp
        | succ j ih =>
            rw [Finset.sum_range_succ, ih]
            ring
      rw [hTel n]
