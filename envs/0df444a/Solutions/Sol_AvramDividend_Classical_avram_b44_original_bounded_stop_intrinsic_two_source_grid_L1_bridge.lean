-- Prove2me | solution 1 for AvramDividend.Classical.avram_b44_original_bounded_stop_intrinsic_two_source_grid_L1_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:06:17.775196+00:00
-- url     : https://prove2.me/submissions/b890e89f-7ff7-4366-aa0f-f334678dc29c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_rightcont_upper_grid_stops
import Theorems.Thm_AvramDividend_Classical_avram_b41_original_finite_range_two_source_L1_stop_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original bounded stopped mixed noise has finite upper-grid approximants whose L1 limits are centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
    ∃ (ρ : ℕ → Ω → ℝ≥0) (S : ℕ → Finset ℝ≥0)
      (R Jsmall : ℕ → ℝ≥0 → Ω → ℝ) (M : ℕ → Ω → ℝ),
      (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ k ω : WithTop ℝ≥0))) ∧
      (∀ k ω, ρ k ω ∈ S k) ∧
      (∀ k ω, τ ω ≤ ρ k ω ∧ ρ k ω ≤ (n : ℝ≥0)) ∧
      (∀ ω, Tendsto (fun k => ρ k ω) atTop (𝓝 (τ ω))) ∧
      (∀ k, Integrable (M k) P ∧
        (∫ ω in A, M k ω ∂P) = 0 ∧
        (∀ ω, M k ω =
          R k (ρ k ω) ω + Jsmall k (ρ k ω) ω)) ∧
      (∀ (Z : Ω → ℝ), Integrable Z P →
        Tendsto (fun k => ∫⁻ ω in A,
          ‖M k ω - Z ω‖ₑ ∂P) atTop (𝓝 (0 : ℝ≥0∞)) →
        (∫ ω in A, Z ω ∂P) = 0) := by 
  classical
  obtain ⟨ρ, hStop, hFiniteRange, hGe, hLe, hLimit⟩ :=
    avram_ja18_original_rightcont_upper_grid_stops
      τ hτstop n hτbound
  choose S hRange using hFiniteRange
  obtain ⟨R, Jsmall, M, hSources, hMeanLimit⟩ :=
    avram_b41_original_finite_range_two_source_L1_stop_limit
      X hX hFinite n hn ρ hStop hLe S hRange A hA
  refine ⟨ρ, S, R, Jsmall, M, hStop, hRange, ?_, hLimit,
    hSources, hMeanLimit⟩
  exact fun k ω => ⟨hGe k ω, hLe k ω⟩
