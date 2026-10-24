-- Prove2me | solution 1 for AvramDividend.Classical.dividendMeasure_continuous_nonzero_not_rightJump_concentrated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:41:46.239654+00:00
-- url     : https://prove2.me/submissions/e5293e85-f48b-4259-8538-201a4bc48f78

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (S : Set ℝ)
    (hS : S = {t : ℝ | 0 ≤ t ∧
      rightLimit D t.toNNReal ω ≠ D t.toNNReal ω})
    (hContinuous : ∀ t : ℝ≥0, rightLimit D t ω = D t ω)
    (a b : ℝ) (hPositive : dividendMeasure D ω (Ioc a b) ≠ 0) :
    (dividendMeasure D ω).restrict S ≠ dividendMeasure D ω := by
  have hEmpty : S = ∅ := by
    rw [hS]
    ext t
    simp [hContinuous t.toNNReal]
  intro hEq
  have hm := congrArg (fun μ : Measure ℝ => μ (Ioc a b)) hEq
  rw [hEmpty] at hm
  simp only [Measure.restrict_empty, zero_apply] at hm
  exact hPositive hm.symm
