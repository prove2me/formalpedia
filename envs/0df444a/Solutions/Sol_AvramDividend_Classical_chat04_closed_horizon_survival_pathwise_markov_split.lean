-- Prove2me | solution 1 for AvramDividend.Classical.chat04_closed_horizon_survival_pathwise_markov_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T22:23:44.549956+00:00
-- url     : https://prove2.me/submissions/eed01d6b-2039-448d-b798-3f8c33ba144a

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Pathwise dynamic-programming split for survival on the closed horizon
[0,u] into an observable F_s history and the future increment-path
survival over [s,u]. No distributional Markov or harmonicity assumptions
are smuggled into this purely pathwise identity.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s u : ℝ≥0) (hsu : s ≤ u)
    (x lower upper : ℝ) :
    {ω | ∀ v : ℝ≥0, v ≤ u →
      ¬ (x + X.X v ω < lower ∨ upper < x + X.X v ω)} =
      {ω | ∀ v : ℝ≥0, v ≤ s →
        ¬ (x + X.X v ω < lower ∨ upper < x + X.X v ω)} ∩
      {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        ¬ ((x + X.X s ω) + (X.X v ω - X.X s ω) < lower ∨
          upper < (x + X.X s ω) + (X.X v ω - X.X s ω))} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro h
    constructor
    · intro v hvs
      exact h v (hvs.trans hsu)
    · intro v hsv hvu
      have heq :
          (x + X.X s ω) + (X.X v ω - X.X s ω) = x + X.X v ω := by
        ring
      simpa only [heq] using h v hvu
  · rintro ⟨hpast, hfuture⟩ v hvu
    rcases le_total v s with hvs | hsv
    · exact hpast v hvs
    · have heq :
          (x + X.X s ω) + (X.X v ω - X.X s ω) = x + X.X v ω := by
        ring
      simpa only [heq] using hfuture v hsv hvu
