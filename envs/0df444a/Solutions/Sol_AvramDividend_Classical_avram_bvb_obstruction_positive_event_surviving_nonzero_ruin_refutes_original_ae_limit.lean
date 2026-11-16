-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_positive_event_surviving_nonzero_ruin_refutes_original_ae_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:01:03.686093+00:00
-- url     : https://prove2.me/submissions/a5405cbe-28ee-422b-8e8e-58f26b9ce769

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal Topology
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : Set Ω) (τ : Ω → ℝ≥0∞) (A : ℕ → Ω → ℝ)
    (hPositive : 0 < P E)
    (hSurvive : ∀ ω ∈ E, τ ω ≠ 0)
    (hBad : ∀ ω ∈ E,
      ¬ Tendsto (fun n => max (A n ω) 0) atTop (𝓝 (0 : ℝ))) :
    ¬ (∀ᵐ ω ∂P, Tendsto
      (fun n => if τ ω = 0 then 0 else max (A n ω) 0)
      atTop (𝓝 (0 : ℝ))) := by
  intro hAe
  have hZero : P {ω | ¬ Tendsto
      (fun n => if τ ω = 0 then 0 else max (A n ω) 0)
      atTop (𝓝 (0 : ℝ))} = 0 := (ae_iff).mp hAe
  have hSubset : E ⊆ {ω | ¬ Tendsto
      (fun n => if τ ω = 0 then 0 else max (A n ω) 0)
      atTop (𝓝 (0 : ℝ))} := by
    intro ω hω
    simpa [hSurvive ω hω] using hBad ω hω
  have hMono : P E ≤ P {ω | ¬ Tendsto
      (fun n => if τ ω = 0 then 0 else max (A n ω) 0)
      atTop (𝓝 (0 : ℝ))} := measure_mono hSubset
  rw [hZero] at hMono
  exact (not_le_of_gt hPositive) hMono
