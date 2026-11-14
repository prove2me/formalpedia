-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a171_finite_measurable_nonnegative_mask_subselection_preserves_L1_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:57:48.855618+00:00
-- url     : https://prove2.me/submissions/29167a4e-dc38-44ae-8bd7-cc12f4824da7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a213_finite_measurable_positive_mask_restriction_preserves_expected_L1_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℕ → Finset ℕ)
    (A B : ℕ → ℕ → Ω → Prop)
    [∀ m i, DecidablePred (A m i)] [∀ m i, DecidablePred (B m i)]
    (f : ℕ → ℕ → Ω → ℝ)
    (hBA : ∀ m i ω, B m i ω → A m i ω)
    (hfNonneg : ∀ m i ω, 0 ≤ f m i ω)
    (hfMeas : ∀ m i, Measurable (f m i))
    (hBMeas : ∀ m i, MeasurableSet {ω : Ω | B m i ω})
    (hAI : ∀ m, Integrable (fun ω =>
      ∑ i ∈ S m, if A m i ω then f m i ω else 0) P)
    (hALim : Tendsto (fun m =>
      ∫ ω, (∑ i ∈ S m, if A m i ω then f m i ω else 0) ∂P)
      atTop (𝓝 (0 : ℝ))) :
    (∀ m, Integrable (fun ω =>
      ∑ i ∈ S m, if B m i ω then f m i ω else 0) P) ∧
    Tendsto (fun m =>
      ∫ ω, (∑ i ∈ S m, if B m i ω then f m i ω else 0) ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  exact avram_ga_a213_finite_measurable_positive_mask_restriction_preserves_expected_L1_zero
    P S A B f hBA hfNonneg hfMeas hBMeas hAI hALim
