-- Prove2me | solution 1 for AvramDividend.Classical.riskProcess_negative_persists_right
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T13:26:06.732727+00:00
-- url     : https://prove2.me/submissions/b6b5f49f-f103-491d-b0d0-bb4917053b96

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hmono : ∀ ω, Monotone (fun t => D t ω))
    (ω : Ω) (t : ℝ≥0)
    (hneg : riskProcess X x D t ω < 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℝ≥0, t ≤ s → dist s t < δ →
        riskProcess X x D s ω < 0 := by
  let ε : ℝ := (D t ω - x - X.X t ω) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    unfold riskProcess at hneg
    linarith
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.continuousWithinAt_iff.mp (X.rightCont ω t)) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro s hts hdist
  have hXclose : dist (X.X s ω) (X.X t ω) < ε :=
    hclose hts hdist
  have hXdiff : X.X s ω - X.X t ω < ε := by
    have habs : |X.X s ω - X.X t ω| < ε := by
      simpa only [Real.dist_eq] using hXclose
    exact (abs_lt.mp habs).2
  have hDmono : D t ω ≤ D s ω := hmono ω hts
  unfold riskProcess
  dsimp [ε] at hXdiff
  change x + X.X t ω - D t ω < 0 at hneg
  linarith
