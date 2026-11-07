-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f14_original_sigma_family_bounded_and_preruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:45:59.116039+00:00
-- url     : https://prove2.me/submissions/4ba73440-86d9-4a2b-8e3d-536c30ca47e2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k ω,
      σ k ω ≤ (n : ℝ≥0) ∧
      (σ k ω : ℝ≥0∞) ≤ ruinTime X x D ω := by
  intro k ω
  obtain ⟨_, hN, hR⟩ :=
    avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n
  have hFinite : τ ω ≤ (n : ℝ≥0) := by
    rw [hτeq ω]
    exact hN ω
  have hBefore : (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω := by
    rw [hτeq ω]
    exact hR ω
  refine ⟨le_trans (hσle k ω) hFinite, ?_⟩
  have hCast : (σ k ω : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) :=
    (ENNReal.coe_le_coe).mpr (hσle k ω)
  exact le_trans hCast hBefore
