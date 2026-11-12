-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB62_uniform_mesh_increment_telescopes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:55:57.709454+00:00
-- url     : https://prove2.me/submissions/d70ff4a8-8ee3-41fc-a9f4-721607ca4117

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem solution
    (a : ℕ → ℝ) (base k : ℕ) :
    (Finset.range k).sum (fun r =>
      a (base + r + 1) - a (base + r)) =
      a (base + k) - a base := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.add_succ]
      ring
