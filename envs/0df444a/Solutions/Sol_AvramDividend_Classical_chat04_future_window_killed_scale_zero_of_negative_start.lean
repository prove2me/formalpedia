-- Prove2me | solution 1 for AvramDividend.Classical.chat04_future_window_killed_scale_zero_of_negative_start
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:55:28.719135+00:00
-- url     : https://prove2.me/submissions/7d67cf8d-4c06-4682-b20f-be2ce6b13b36

import Mathlib.Algebra.Notation.Indicator
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! A negative reserve at the start of the future window kills its payoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ) (s u : ℝ≥0)
    (hsu : s ≤ u) (ω : Ω) (hneg : x + X.X s ω < 0) :
    ({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
       0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω)) ω = 0 := by
  have hnot : ω ∉
      {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)} := by
    intro h
    have h0 :
        0 ≤ (x + X.X s ω) + (X.X s ω - X.X s ω) :=
      h s le_rfl hsu
    have hs : 0 ≤ x + X.X s ω := by
      simpa only [sub_self, add_zero] using h0
    exact (not_le.mpr hneg) hs
  exact Set.indicator_of_notMem hnot _
