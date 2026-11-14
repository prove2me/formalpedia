-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a58_true_stop_positive_taylor_expected_energy_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:15:40.235711+00:00
-- url     : https://prove2.me/submissions/3b2301c3-cea4-4d07-8ed5-a609eb59166c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a44_true_stop_mask_positive_taylor_small_large_split
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Expected positive stopped Gaussian Taylor energy is controlled by total and rare-large quadratic energies. -/
theorem solution
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : Finset ι) (s : ι → ℝ≥0) (ρ : Ω → ℝ≥0)
    (a z : ι → Ω → ℝ) (ε M δ : ℝ)
    (hε : 0 ≤ ε)
    (ha : ∀ ω : Ω, ∀ i ∈ S, s i < ρ ω → 0 ≤ a i ω)
    (hM : ∀ ω : Ω, ∀ i ∈ S, s i < ρ ω → a i ω ≤ M)
    (hSmall : ∀ ω : Ω, ∀ i ∈ S, s i < ρ ω →
      |z i ω| < δ → a i ω ≤ ε) :
    let A : Ω → ℝ := fun ω =>
      ∑ i ∈ S, if s i < ρ ω then a i ω * (z i ω)^2 else 0
    let E : Ω → ℝ := fun ω =>
      ∑ i ∈ S, if s i < ρ ω then (z i ω)^2 else 0
    let T : Ω → ℝ := fun ω =>
      ∑ i ∈ S, if s i < ρ ω then
        (if δ ≤ |z i ω| then (z i ω)^2 else 0) else 0
    Integrable A P → Integrable E P → Integrable T P →
      (∫ ω, A ω ∂P) ≤ ε * (∫ ω, E ω ∂P) +
        M * (∫ ω, T ω ∂P) := by
  classical
  let A : Ω → ℝ := fun ω =>
    ∑ i ∈ S, if s i < ρ ω then a i ω * (z i ω)^2 else 0
  let E : Ω → ℝ := fun ω =>
    ∑ i ∈ S, if s i < ρ ω then (z i ω)^2 else 0
  let T : Ω → ℝ := fun ω =>
    ∑ i ∈ S, if s i < ρ ω then
      (if δ ≤ |z i ω| then (z i ω)^2 else 0) else 0
  change Integrable A P → Integrable E P → Integrable T P →
      (∫ ω, A ω ∂P) ≤ ε * (∫ ω, E ω ∂P) +
        M * (∫ ω, T ω ∂P)
  intro hA hE hT
  have hBound (ω : Ω) : A ω ≤ ε * E ω + M * T ω :=
    avram_ga_a44_true_stop_mask_positive_taylor_small_large_split
      S s ρ ω a z ε M δ hε (ha ω) (hM ω) (hSmall ω)
  calc
    (∫ ω, A ω ∂P) ≤ (∫ ω, ε * E ω + M * T ω ∂P) :=
      integral_mono hA ((hE.const_mul ε).add (hT.const_mul M)) hBound
    _ = ε * (∫ ω, E ω ∂P) + M * (∫ ω, T ω ∂P) := by
      rw [integral_add (hE.const_mul ε) (hT.const_mul M)]
      rw [integral_const_mul, integral_const_mul]
