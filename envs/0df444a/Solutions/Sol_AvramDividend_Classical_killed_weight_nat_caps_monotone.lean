-- Prove2me | solution 1 for AvramDividend.Classical.killed_weight_nat_caps_monotone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:18:43.121466+00:00
-- url     : https://prove2.me/submissions/8e864af9-8f09-4ff2-beb3-4a7bc855084c

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} (T : Ω → ℝ≥0∞) (weight : Ω → ℝ≥0∞) :
    Monotone (fun n : ℕ => fun ω : Ω =>
      if T ω ≤ (n : ℝ≥0∞) then weight ω else 0) := by 
  intro m n hmn ω
  simp only
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h1.trans (by exact_mod_cast hmn)) h2
  · exact zero_le
  · exact le_rfl
