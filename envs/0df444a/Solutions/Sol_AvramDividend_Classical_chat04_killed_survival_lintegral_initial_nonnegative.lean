-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_survival_lintegral_initial_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:26:48.658328+00:00
-- url     : https://prove2.me/submissions/a5a89b3a-15cd-41d7-9e97-1f1b44edb02c

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (x : ℝ) (hx : 0 ≤ x) :
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ (0 : ℝ≥0) → 0 ≤ x + X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (-(q * ((0 : ℝ≥0) : ℝ))) * W (x + X.X 0 ω))) ω ∂P) =
      ENNReal.ofReal (W x) := by
  haveI : IsProbabilityMeasure P := X.isProbability
  have hsurv : {ω : Ω | ∀ s : ℝ≥0, s ≤ (0 : ℝ≥0) →
      0 ≤ x + X.X s ω} = Set.univ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro s hs
    have hs0 : s = 0 := le_antisymm hs bot_le
    subst s
    simpa [X.X_zero] using hx
  simp [hsurv, X.X_zero, hx]
