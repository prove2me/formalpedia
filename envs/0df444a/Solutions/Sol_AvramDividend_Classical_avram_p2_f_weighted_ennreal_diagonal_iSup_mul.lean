-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_ennreal_diagonal_iSup_mul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:33:31.006529+00:00
-- url     : https://prove2.me/submissions/1a325e52-ffc9-4964-a1bc-1f258910c3fd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Directed diagonal continuity of ENNReal multiplication, including
zero times infinity, for two increasing sequences. -/
theorem solution
    (a b : ℕ → ℝ≥0∞)
    (ha : Monotone a) (hb : Monotone b) :
    (⨆ n, a n) * (⨆ n, b n) = ⨆ n, a n * b n := by
  apply le_antisymm
  · rw [ENNReal.iSup_mul]
    refine iSup_le fun i => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun j => ?_
    calc
      a i * b j ≤ a (max i j) * b j :=
        mul_le_mul_of_nonneg_right (ha (Nat.le_max_left i j)) zero_le
      _ ≤ a (max i j) * b (max i j) :=
        mul_le_mul_of_nonneg_left (hb (Nat.le_max_right i j)) zero_le
      _ ≤ ⨆ n, a n * b n := le_iSup (fun n => a n * b n) (max i j)
  · refine iSup_le fun i => ?_
    calc
      a i * b i ≤ (⨆ n, a n) * b i :=
        mul_le_mul_of_nonneg_right (le_iSup a i) zero_le
      _ ≤ (⨆ n, a n) * (⨆ n, b n) :=
        mul_le_mul_of_nonneg_left (le_iSup b i) zero_le
