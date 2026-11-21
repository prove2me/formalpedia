-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_fixedband_arbitrarily_small_signed_L1_forces_zero_positive_excess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:45:21.015759+00:00
-- url     : https://prove2.me/submissions/3dc807c3-853d-4512-8d0b-f0f0f140b523

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward80g_upper_L1_to_positive_gap
open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

/-- A signed upper-L1 physical source with the same comparator for every
arbitrarily small tolerance forces zero positive original reward excess. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (G U : Ω → ℝ)
    (hGapI : Integrable (fun ω => G ω - U ω) P)
    (hSource : ∀ ε : ℝ, 0 < ε →
      ∃ (K : Ω → ℝ) (E : ℕ → Ω → ℝ),
        Integrable K P ∧
        (∫ ω, |K ω| ∂P) ≤ ε / 4 ∧
        (∀ k, Integrable (E k) P) ∧
        (∀ k, ∀ᵐ ω ∂P,
          G ω - U ω ≤ K ω + E k ω) ∧
        Tendsto (fun k : ℕ =>
          ∫ ω, |E k ω| ∂P)
          Filter.atTop (𝓝 (0 : ℝ))) :
    (∫ ω, max (0 : ℝ) (G ω - U ω) ∂P) = 0 := by
  have hNonneg : (0 : ℝ) ≤
      (∫ ω, max (0 : ℝ) (G ω - U ω) ∂P) :=
    integral_nonneg (fun ω => le_max_left _ _)
  apply le_antisymm ?_ hNonneg
  by_contra hNot
  have hp : 0 < (∫ ω, max (0 : ℝ) (G ω - U ω) ∂P) := by
    exact lt_of_not_ge hNot
  obtain ⟨K, E, hKI, hKsmall, hEI, hUpper, hVan⟩ :=
    hSource _ hp
  have hBound :=
    avram_pj_reward80g_upper_L1_to_positive_gap
      P G U G _ hp ⟨K, E, hKI, hKsmall, hEI, hUpper, hVan⟩
      hGapI (by
        filter_upwards [] with ω
        exact le_max_right _ _)
  linarith
