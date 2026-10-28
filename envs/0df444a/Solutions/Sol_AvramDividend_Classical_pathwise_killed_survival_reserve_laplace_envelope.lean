-- Prove2me | solution 1 for AvramDividend.Classical.pathwise_killed_survival_reserve_laplace_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:57:00.019864+00:00
-- url     : https://prove2.me/submissions/57e92db9-ffe0-419d-a5d9-2cf7c4c2218c

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_lower_survival_running_infimum_equiv
import Theorems.Thm_AvramDividend_Classical_lower_survival_nonstrict_reserve_integral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-- Integrating the full finite-horizon survival event over initial reserves
gives the explicit running-infimum Laplace envelope, path by path. -/
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
  let m : ℝ := sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω}
  have hset :
      {x : ℝ | 0 < x ∧ ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω} =
      {x : ℝ | 0 < x ∧ 0 ≤ x + m} := by
    ext x
    simp only [mem_setOf_eq]
    constructor
    · rintro ⟨hx, hsurv⟩
      exact ⟨hx, (lower_survival_running_infimum_equiv X t ω hb x).mp hsurv⟩
    · rintro ⟨hx, hmin⟩
      exact ⟨hx, (lower_survival_running_infimum_equiv X t ω hb x).mpr hmin⟩
  rw [hset]
  exact lower_survival_nonstrict_reserve_integral m θ hθ
