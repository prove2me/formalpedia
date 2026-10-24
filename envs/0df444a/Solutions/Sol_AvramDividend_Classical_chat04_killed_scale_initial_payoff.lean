-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_scale_initial_payoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:57:28.063269+00:00
-- url     : https://prove2.me/submissions/dae840cc-17ad-4da1-a147-3187920da48d

import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (hx : 0 ≤ x) (W : ℝ → ℝ) :
    ∀ ω : Ω,
      ({ω | ∀ s : ℝ≥0, s ≤ (0 : ℝ≥0) → 0 ≤ x + X.X s ω}.indicator
        (fun ω => Real.exp (-(q * ((0 : ℝ≥0) : ℝ))) *
          W (x + X.X (0 : ℝ≥0) ω)) ω) = W x := by
  intro ω
  have hsurv : ω ∈
      {ω : Ω | ∀ s : ℝ≥0, s ≤ (0 : ℝ≥0) → 0 ≤ x + X.X s ω} := by
    intro s hs
    have hs0 : s = 0 := le_antisymm hs (by positivity)
    subst s
    simpa only [X.X_zero ω, add_zero] using hx
  rw [Set.indicator_of_mem hsurv]
  simp only [NNReal.coe_zero, mul_zero, neg_zero, Real.exp_zero, one_mul,
    X.X_zero ω, add_zero]
