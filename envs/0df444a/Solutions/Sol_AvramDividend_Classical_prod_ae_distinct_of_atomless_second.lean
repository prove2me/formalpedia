-- Prove2me | solution 1 for AvramDividend.Classical.prod_ae_distinct_of_atomless_second
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:06:48.31777+00:00
-- url     : https://prove2.me/submissions/4e0db407-f04c-416d-b4a9-87df014eebc0

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Probability.IdentDistrib

open MeasureTheory
open scoped ENNReal
theorem solution
    (μ ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν] :
    ∀ᵐ p ∂μ.prod ν, p.1 ≠ p.2 := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  have hs : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} := measurableSet_diagonal
  rw [Measure.prod_apply hs]
  have : ∀ x : ℝ, ν (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 0 := by
    intro x
    have : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {x} := by
      ext y; simp [eq_comm]
    rw [this]; exact measure_singleton x
  simp [this]
