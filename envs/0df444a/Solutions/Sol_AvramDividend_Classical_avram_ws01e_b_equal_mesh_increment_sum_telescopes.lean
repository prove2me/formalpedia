-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_equal_mesh_increment_sum_telescopes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:07:40.92051+00:00
-- url     : https://prove2.me/submissions/e86b83f3-a006-4a91-a973-5d054fdcb293

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℝ≥0) (n : ℕ) (ω : Ω) :
    Finset.sum (Finset.range n) (fun j =>
      X.X ((((j + 1 : ℕ) : ℝ≥0) * δ)) ω -
      X.X (((j : ℝ≥0) * δ)) ω) =
      X.X (((n : ℝ≥0) * δ)) ω - X.X 0 ω := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
