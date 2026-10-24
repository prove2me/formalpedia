-- Prove2me | solution 1 for AvramDividend.Classical.chat04_lower_killing_history_future_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T20:55:38.401852+00:00
-- url     : https://prove2.me/submissions/b90c93a3-f83e-4310-87b9-6397d3a6afd5

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-! The one-sided ruin-killing event splits at every deterministic time,
including both endpoints. This is the exact survival rule used by the
killed q-scale martingale target. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    {ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω} =
      {ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω} ∩
      {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
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
