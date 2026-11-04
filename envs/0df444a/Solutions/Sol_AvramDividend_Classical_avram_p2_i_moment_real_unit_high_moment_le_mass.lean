-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_real_unit_high_moment_le_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:48:14.502676+00:00
-- url     : https://prove2.me/submissions/752991ee-6010-4a5b-9173-c5be9a5001a1

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

theorem solution
    (μ : Measure ℝ) (hμ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (hOne : Integrable (fun _ : ℝ => (1 : ℝ)) μ)
    (k : ℕ) (hk : Integrable (fun z : ℝ => z ^ k) μ) :
    (∫ z : ℝ, z ^ k ∂μ) ≤ (∫ _ : ℝ, (1 : ℝ) ∂μ) := by
  have hpow : ∀ᵐ z ∂μ, z ^ k ≤ (1 : ℝ) := by
    filter_upwards [hμ] with z hz
    have hz_nonneg : 0 ≤ z := hz.1
    have hz_le : z ≤ (1 : ℝ) := hz.2
    have hbound : z ^ k ≤ (1 : ℝ) ^ k := by
      gcongr
    simpa using hbound
  exact integral_mono_ae hk hOne hpow
