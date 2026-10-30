-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_actual_surviving_cap_killed_reward_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:44:42.497616+00:00
-- url     : https://prove2.me/submissions/5cd39cb3-87c0-47e8-9b0a-965b3fa34d3f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- On a true surviving-cap path, every sampled stopping history below
the cap survives; the history-killed reward equals the unrestricted reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (x : ℝ) (T : ℝ≥0) (t : ℕ → ℝ≥0)
    (ht : ∀ n, t n ≤ T)
    (hBefore : ∀ s : ℝ≥0, s ≤ T → 0 ≤ x + X.X s ω)
    (q : ℝ) (W : ℝ → ℝ) (y : ℝ)
    (hRaw : Tendsto (fun n =>
      Real.exp (-(q * (t n : ℝ))) * W (x + X.X (t n) ω))
      atTop (nhds y)) :
    Tendsto (fun n =>
      ({η : Ω | ∀ s : ℝ≥0, s ≤ t n → 0 ≤ x + X.X s η}).indicator
        (fun η => Real.exp (-(q * (t n : ℝ))) *
          W (x + X.X (t n) η)) ω) atTop (nhds y) := by
  have hSurv (n : ℕ) :
      ω ∈ {η : Ω | ∀ s : ℝ≥0,
        s ≤ t n → 0 ≤ x + X.X s η} := by
    intro s hs
    exact hBefore s (hs.trans (ht n))
  have hEq : (fun n =>
      ({η : Ω | ∀ s : ℝ≥0, s ≤ t n → 0 ≤ x + X.X s η}).indicator
        (fun η => Real.exp (-(q * (t n : ℝ))) *
          W (x + X.X (t n) η)) ω) =
      (fun n => Real.exp (-(q * (t n : ℝ))) *
          W (x + X.X (t n) ω)) := by
    funext n
    exact Set.indicator_of_mem (hSurv n) _
  rw [hEq]
  exact hRaw
