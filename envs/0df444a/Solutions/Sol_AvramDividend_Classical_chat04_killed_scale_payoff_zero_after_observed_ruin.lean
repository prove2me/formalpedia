-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_scale_payoff_zero_after_observed_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:49:59.45531+00:00
-- url     : https://prove2.me/submissions/ae01be27-7a3b-4cf5-b2b0-fe05d254b165

import Mathlib.Algebra.Notation.Indicator
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! After an observed negative reserve, all later killed payoffs vanish. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ) (s t : ℝ≥0)
    (hst : s ≤ t) (ω : Ω) (hneg : x + X.X s ω < 0) :
    ({u : Ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v u}).indicator
      (fun u => Real.exp (-(q * (t : ℝ))) * W (x + X.X t u)) ω = 0 := by
  have hnot : ω ∉
      {u : Ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v u} := by
    intro h
    exact (not_le.mpr hneg) (h s hst)
  exact Set.indicator_of_notMem hnot _
