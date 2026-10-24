-- Prove2me | solution 1 for AvramDividend.Classical.chat04_all_n_levy_increment_telescoping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:18:48.416676+00:00
-- url     : https://prove2.me/submissions/df9f6b0c-7e43-4563-97d0-9ef6f0412729

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-! Consecutive increments telescope along any finite observation sequence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℕ → ℝ≥0) (n : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range n,
      (X.X (t (i + 1)) ω - X.X (t i) ω)) =
      X.X (t n) ω - X.X (t 0) ω := by
  induction n with
  | zero =>
      simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      ring
