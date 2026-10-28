-- Prove2me | solution 2 for AvramDividend.Classical.pathwise_killed_survival_reserve_laplace_envelope
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:57:04.763287+00:00
-- url     : https://prove2.me/submissions/3cc2523e-58f2-4e43-bb63-b2b42b0a590f

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_lower_survival_running_infimum_equiv
import Theorems.Thm_AvramDividend_Classical_lower_survival_nonstrict_reserve_integral

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ω : Ω)
    (hb : BddBelow {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})
    (θ : ℝ) (hθ : 0 < θ) :
    (∫ x in {x : ℝ | 0 < x ∧
        ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}, Real.exp (-θ * x)) =
      Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / θ := by 
  have e : {x : ℝ | 0 < x ∧ ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω} =
      {x : ℝ | 0 < x ∧ 0 ≤ x + sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω}} := by
    ext x
    simp only [mem_setOf_eq, lower_survival_running_infimum_equiv X t ω hb x]
  rw [e]
  exact lower_survival_nonstrict_reserve_integral _ θ hθ
