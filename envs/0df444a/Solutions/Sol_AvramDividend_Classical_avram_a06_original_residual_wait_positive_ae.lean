-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_residual_wait_positive_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T15:58:17.620806+00:00
-- url     : https://prove2.me/submissions/5602a58d-c037-41cd-9b80-4ddd7f16e006

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Theorems.Thm_AvramDividend_Classical_avram_a06_threshold_residual_strict_positive_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (τ : ℕ → Ω → ℝ) (N : Ω → ℝ → ℕ)
    (hThresholdAE : ∀ᵐ ω ∂P, ∀ u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) :
    ∀ᵐ ω ∂P,
      0 < τ (N ω clock) ω -
        (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) := by
  exact AvramDividend.Classical.avram_a06_threshold_residual_strict_positive_ae
    P τ N hThresholdAE clock
