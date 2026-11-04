-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_source_interval_horizon_clip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:40:16.087389+00:00
-- url     : https://prove2.me/submissions/94796f95-bccd-4b7b-8248-090910834c56

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (s t T : ℝ≥0) :
    (Ioc s t ∩ Iic T) = Ioc s (min t T) := by
  ext u
  simp only [mem_inter_iff, mem_Ioc, mem_Iic, le_min_iff, and_assoc]
