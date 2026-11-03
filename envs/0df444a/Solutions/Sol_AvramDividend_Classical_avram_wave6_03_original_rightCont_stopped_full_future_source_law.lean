-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_full_future_source_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:24:46.36885+00:00
-- url     : https://prove2.me/submissions/6ce56c2e-22d0-43eb-b05b-d99c4da8cbcf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_shiftedFuturePath_sameLaw

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s}) :
    Measure.map (fun ω : Ω => fun t : ℝ≥0 =>
      X.X (τ ω + t) ω - X.X (τ ω) ω) P =
    Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P := by
  obtain ⟨Y, hYpath, -, -, -⟩ :=
    AvramDividend.Classical.avram_wave5_04_source_rightCont_levy_lift X
  simpa only [hYpath] using
    (AvramDividend.Classical.levy_finiteStopping_shiftedFuturePath_sameLaw Y τ hτ)
