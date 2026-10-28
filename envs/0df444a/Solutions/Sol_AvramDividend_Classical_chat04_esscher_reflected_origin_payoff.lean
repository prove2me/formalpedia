-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_reflected_origin_payoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:04:30.109353+00:00
-- url     : https://prove2.me/submissions/325b39e8-72b4-482e-86ef-d6a0dc83689e

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (β θ : ℝ) (hβ : 0 < β) :
    (Real.exp (-β * max 0
      (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ (0 : ℝ≥0) ∧ y = X.X s ω})) / β) *
    Real.exp (θ * X.X 0 ω -
      ((0 : ℝ≥0) : ℝ) * laplaceExponent X.c X.σ X.ν θ) =
    1 / β := by
  have hRange :
      {y : ℝ | ∃ s : ℝ≥0, s ≤ (0 : ℝ≥0) ∧ y = X.X s ω} =
        ({0} : Set ℝ) := by
    ext y
    constructor
    · rintro ⟨s, hs, hy⟩
      have hs0 : s = 0 := le_zero_iff.mp hs
      subst s
      simpa [X.X_zero ω] using hy
    · intro hy
      have hy0 : y = 0 := by simpa using hy
      subst y
      exact ⟨0, le_refl _, (X.X_zero ω).symm⟩
  simp [hRange, X.X_zero ω]
