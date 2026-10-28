-- Prove2me | solution 1 for AvramDividend.Classical.lower_survival_running_infimum_equiv
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:43:02.958643+00:00
-- url     : https://prove2.me/submissions/4a9a8b22-8511-4ed2-8b79-a34253bd0ab1

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ω : Ω)
    (hb : BddBelow {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})
    (x : ℝ) :
    (∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω) ↔
      0 ≤ x + sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω} := by 
  have hne : ({y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω}).Nonempty := ⟨_, 0, zero_le, rfl⟩
  constructor
  · intro h
    have : -x ≤ sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω} := by
      apply le_csInf hne
      rintro y ⟨s, hs, rfl⟩
      linarith [h s hs]
    linarith
  · intro h s hs
    have := csInf_le hb ⟨s, hs, rfl⟩
    linarith
