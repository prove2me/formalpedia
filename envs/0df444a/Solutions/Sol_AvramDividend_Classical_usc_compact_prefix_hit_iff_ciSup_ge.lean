-- Prove2me | solution 1 for AvramDividend.Classical.usc_compact_prefix_hit_iff_ciSup_ge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:23:10.285091+00:00
-- url     : https://prove2.me/submissions/5d02fc71-0474-4256-9ced-a56376636ce7

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_usc_compact_prefix_hit_iff_sup_ge
open AvramDividend.Classical Set Topology
open scoped NNReal
theorem solution
    (R : ℝ≥0 → ℝ) (t : ℝ≥0) (x : ℝ)
    (husc : UpperSemicontinuousOn R (Icc 0 t)) :
    (∃ s : ℝ≥0, s ≤ t ∧ x ≤ R s) ↔
      x ≤ ⨆ s : Set.Icc (0 : ℝ≥0) t, R s.1 := by
  rw [usc_compact_prefix_hit_iff_sup_ge R t x husc, sSup_image']
