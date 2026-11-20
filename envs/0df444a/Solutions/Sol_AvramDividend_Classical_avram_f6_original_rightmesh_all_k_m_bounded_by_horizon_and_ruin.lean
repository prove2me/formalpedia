-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_rightmesh_all_k_m_bounded_by_horizon_and_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:55:29.330992+00:00
-- url     : https://prove2.me/submissions/98055166-b1d1-4284-9e50-80ba3b3d4f8a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ (k m : ℕ) (ω : Ω),
      let ρ : ℝ≥0 := min (τ ω)
        (σ k ω + (1 : ℝ≥0) / ((m : ℝ≥0) + 1))
      ρ ≤ (n : ℝ≥0) ∧
        (ρ : ℝ≥0∞) ≤ ruinTime X x D ω := by
  intro k m ω
  dsimp only
  have hρle : ∀ η : Ω,
      min (τ η) (σ k η + (1 : ℝ≥0) / ((m : ℝ≥0) + 1)) ≤ τ η :=
    fun η => min_le_left _ _
  exact ⟨
    (avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
      X x C D hD n hn τ
      (fun η => min (τ η) (σ k η + (1 : ℝ≥0) / ((m : ℝ≥0) + 1)))
      hτeq hρle).1 ω,
    (avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
      X x C D hD n hn τ
      (fun η => min (τ η) (σ k η + (1 : ℝ≥0) / ((m : ℝ≥0) + 1)))
      hτeq hρle).2 ω⟩
