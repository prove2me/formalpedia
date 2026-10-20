-- Prove2me | solution 1 for AvramDividend.Classical.measure_restrict_iUnion_eq_of_countable_directed_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T14:10:36.137011+00:00
-- url     : https://prove2.me/submissions/bc2c704f-fa81-40d8-9214-0290f869bce7

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
open MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {ι : Type*} [Countable ι]
    (μ ν : Measure ℝ) (s : ι → Set ℝ)
    (hd : Directed (· ⊆ ·) s)
    (heq : ∀ i, μ.restrict (s i) = ν.restrict (s i)) :
    μ.restrict (⋃ i, s i) = ν.restrict (⋃ i, s i) := by
  apply Measure.ext
  intro t ht
  rw [μ.restrict_iUnion_apply_eq_iSup hd ht,
      ν.restrict_iUnion_apply_eq_iSup hd ht]
  apply iSup_congr
  intro i
  exact congrArg (fun η : Measure ℝ => η t) (heq i)
