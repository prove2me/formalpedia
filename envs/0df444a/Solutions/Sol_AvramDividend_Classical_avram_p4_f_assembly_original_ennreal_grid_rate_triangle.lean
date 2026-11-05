-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_ennreal_grid_rate_triangle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T22:08:19.939561+00:00
-- url     : https://prove2.me/submissions/3cde9d47-806c-4014-bee8-d26da706c705

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_physical_grid_real_rate_bridge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    (T a : ℝ≥0) (k : ℕ) (hk : 0 < k) :
    let s : Fin k → ℝ≥0 := fun i => ((i.val : ℝ≥0) * T) / (k : ℝ≥0)
    let t : Fin k → ℝ≥0 := fun i => (((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0)
    (∑ i : Fin k, ((s i : ℝ≥0) : ℝ≥0∞) * (a : ℝ≥0∞) *
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * (a : ℝ≥0∞))) =
      ENNReal.ofReal (((k : ℝ) * ((k : ℝ) - 1) / 2) *
        (((T : ℝ) * (a : ℝ)) ^ 2 / (k : ℝ) ^ 2)) := by
  intro s t
  have hreal :
      (∑ i : Fin k, ((s i : ℝ) * (a : ℝ)) *
        (((t i - s i : ℝ≥0) : ℝ) * (a : ℝ))) =
      ((k : ℝ) * ((k : ℝ) - 1) / 2) *
        (((T : ℝ) * (a : ℝ)) ^ 2 / (k : ℝ) ^ 2) := by
    simpa only [s, t] using
      (avram_p4_f_assembly_original_physical_grid_real_rate_bridge T a k hk)
  have hsum :
      (((∑ i : Fin k, (s i * a) * ((t i - s i) * a)) : ℝ≥0) : ℝ) =
      ((k : ℝ) * ((k : ℝ) - 1) / 2) *
        (((T : ℝ) * (a : ℝ)) ^ 2 / (k : ℝ) ^ 2) := by
    simpa only [NNReal.coe_sum, NNReal.coe_mul] using hreal
  let z : ℝ≥0 := ∑ i : Fin k, (s i * a) * ((t i - s i) * a)
  have hz : (z : ℝ) =
      ((k : ℝ) * ((k : ℝ) - 1) / 2) *
        (((T : ℝ) * (a : ℝ)) ^ 2 / (k : ℝ) ^ 2) := hsum
  calc
    (∑ i : Fin k, ((s i : ℝ≥0) : ℝ≥0∞) * (a : ℝ≥0∞) *
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * (a : ℝ≥0∞))) =
      (z : ℝ≥0∞) := by
        dsimp [z]
        norm_cast
    _ = ENNReal.ofReal (z : ℝ) := by
        exact (ENNReal.ofReal_coe_nnreal).symm
    _ = ENNReal.ofReal (((k : ℝ) * ((k : ℝ) - 1) / 2) *
        (((T : ℝ) * (a : ℝ)) ^ 2 / (k : ℝ) ^ 2)) := by
        rw [hz]
