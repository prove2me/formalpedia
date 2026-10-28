-- Prove2me | solution 1 for AvramDividend.Classical.shifted_future_strip_implies_drawdown_guard
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:38:56.026151+00:00
-- url     : https://prove2.me/submissions/98e82b3a-5636-42cd-ab78-35d7d854c6f6

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a ε : ℝ) (ω : Ω) (u T : ℝ≥0)
    (hUpper : ∀ r : ℝ≥0, r ≤ T →
      X.X (u + r) ω - X.X u ω ≤ ε)
    (hLower : ∀ r : ℝ≥0, r ≤ T →
      ε - a ≤ X.X (u + r) ω - X.X u ω) :
    ∀ t : ℝ≥0, t ≤ T →
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
        X.X (u + t) ω ≤ a := by
  intro t ht
  have hS : sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) ≤ X.X u ω + ε := by
    apply csSup_le ((Set.nonempty_Icc.2 (zero_le (a := t))).image _)
    rintro _ ⟨r, hr, rfl⟩
    have := hUpper r (hr.2.trans ht)
    linarith
  have := hLower t ht
  linarith
