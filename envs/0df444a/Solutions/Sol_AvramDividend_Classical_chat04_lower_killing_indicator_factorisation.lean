-- Prove2me | solution 1 for AvramDividend.Classical.chat04_lower_killing_indicator_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T20:55:37.502096+00:00
-- url     : https://prove2.me/submissions/955863ae-7a06-4183-9b80-531e29290890

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Algebra.Notation.Indicator
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-! Exact historical/future indicator product for killed real payoffs.
This is the pathwise input for pulling the historical survival event
through a conditional expectation in the q-scale martingale proof. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) (f : Ω → ℝ) :
    ({ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω}).indicator f =
      ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
        (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
          0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator f) := by
  let A : Set Ω := {ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}
  let B : Set Ω := {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
    0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}
  let D : Set Ω := {ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω}
  have hD : D = A ∩ B := by
    ext ω
    simp only [D, A, B, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro h
      constructor
      · intro v hvs
        exact h v (hvs.trans hsu)
      · intro v hsv hvu
        have heq : (x + X.X s ω) + (X.X v ω - X.X s ω) =
            x + X.X v ω := by ring
        simpa only [heq] using h v hvu
    · rintro ⟨hpast, hfuture⟩ v hvu
      rcases le_total v s with hvs | hsv
      · exact hpast v hvs
      · have heq : (x + X.X s ω) + (X.X v ω - X.X s ω) =
            x + X.X v ω := by ring
        simpa only [heq] using hfuture v hsv hvu
  change D.indicator f = A.indicator (B.indicator f)
  rw [hD]
  funext ω
  by_cases ha : ω ∈ A
  · by_cases hb : ω ∈ B
    · simp [Set.indicator, ha, hb]
    · simp [Set.indicator, ha, hb]
  · simp [Set.indicator, ha]
