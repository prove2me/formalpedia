-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_discounted_scale_initial_value_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:00:25.228234+00:00
-- url     : https://prove2.me/submissions/49330fa5-1a61-4c4b-8d53-3ed3f7546f39

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-! A nonnegative initial reserve survives the zero-length time window,
so the killed discounted q-scale process starts at the canonical W(x). -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (x : ℝ) (hx : 0 ≤ x) (ω : Ω) :
    ({ω | ∀ s : ℝ≥0, s ≤ 0 → 0 ≤ x + X.X s ω}).indicator
      (fun ω => Real.exp (-(q * (0 : ℝ))) *
        W (x + X.X 0 ω)) ω = W x := by
  have hmem : ω ∈
      {ω | ∀ s : ℝ≥0, s ≤ 0 → 0 ≤ x + X.X s ω} := by
    intro s hs
    have hs0 : s = 0 := le_antisymm hs bot_le
    subst s
    simpa only [X.X_zero ω, add_zero] using hx
  simp only [Set.indicator_of_mem hmem, X.X_zero ω, add_zero,
    mul_zero, neg_zero, Real.exp_zero, one_mul]
