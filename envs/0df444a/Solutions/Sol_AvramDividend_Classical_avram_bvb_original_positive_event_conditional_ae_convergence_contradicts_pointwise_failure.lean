-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_original_positive_event_conditional_ae_convergence_contradicts_pointwise_failure
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T15:10:01.616524+00:00
-- url     : https://prove2.me/submissions/74293e76-ea73-44b2-a942-a32854ba22f8

import Mathlib
open Classical MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (E : Set Ω) (τ : Ω → ℝ≥0∞)
    (A : ℕ → Ω → ℝ)
    (hPositive : 0 < P E)
    (hSurvive : ∀ ω ∈ E, τ ω ≠ 0)
    (hFails : ∀ ω ∈ E,
      ¬ Tendsto (fun n => max (A n ω) 0) atTop (𝓝 (0 : ℝ)))
    (hAe : ∀ᵐ ω ∂P, ω ∈ E →
      Tendsto (fun n => if τ ω = 0 then 0
        else max (A n ω) 0) atTop (𝓝 (0 : ℝ))) :
    False := by
  have hnot : ∀ᵐ ω ∂P, ω ∉ E := by
    filter_upwards [hAe] with ω hω hE
    apply hFails ω hE
    have := hω hE
    simpa [hSurvive ω hE] using this
  have h0 : P E = 0 := (measure_eq_zero_iff_ae_notMem).2 hnot
  exact (ne_of_gt hPositive) h0
