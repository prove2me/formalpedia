-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_predictable_grid_energy_L2_to_eventwise_L1_zero_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:27:55.224623+00:00
-- url     : https://prove2.me/submissions/afd0614b-38e1-47c8-aa46-30e7f3d8b317

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_original_grid_smallmark_energy_L2_limit_zero_mean
import Theorems.Thm_AvramDividend_Classical_avram_gb29_probabilistic_L2_to_eventwise_L1_transfer
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ → ℕ) (s t : ℕ → ℕ → ℝ≥0)
    (W : ℕ → ℕ → Ω → ℝ)
    (hWPast : ∀ k, ∀ i ∈ Finset.range (n k),
      Measurable[𝓕 (s k i)] (W k i))
    (hWI : ∀ k, ∀ i ∈ Finset.range (n k), Integrable (W k i) P)
    (hXI : ∀ k, ∀ i ∈ Finset.range (n k), Integrable (X.X (t k i)) P)
    (hCellI : ∀ k, ∀ i ∈ Finset.range (n k), Integrable (fun ω =>
      W k i ω * (X.X (s k i + t k i) ω - X.X (s k i) ω -
        (∫ η, X.X (t k i) η ∂P))) P)
    (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (hSource : ∀ k, (M k : Ω → ℝ) =ᵐ[P] fun ω =>
      ∑ i ∈ Finset.range (n k),
        W k i ω * (X.X (s k i + t k i) ω - X.X (s k i) ω -
          (∫ η, X.X (t k i) η ∂P)))
    (Cband : ℝ)
    (hBandBound : ∀ i j : ℕ, i ≤ j →
      dist (M i) (M j) ≤
        Cband * Real.sqrt ((∫⁻ z in Ioc (-(1 / ((i : ℝ) + 1))) (0 : ℝ),
          ENNReal.ofReal (z ^ 2) ∂X.ν).toReal)) :
    ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto M Filter.atTop (𝓝 L) ∧
      (∫ ω, L ω ∂P) = 0 ∧
      ∀ A : Set Ω,
        Tendsto (fun j : ℕ =>
          ∫ ω in A, |L ω - M j ω| ∂P)
          atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨L, hLim, hMean⟩ :=
    avram_jump6_B_actual_original_grid_smallmark_energy_L2_limit_zero_mean
      X n s t W hWPast hWI hXI hCellI M hSource Cband hBandBound
  refine ⟨L, hLim, hMean, ?_⟩
  intro A
  have hL2 : Tendsto
      (fun j : ℕ => eLpNorm ((M j : Ω → ℝ) - (L : Ω → ℝ)) 2 P)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm
      M (L : Ω → ℝ) (Lp.memLp L)).mp (by simpa using hLim)
  exact avram_gb29_probabilistic_L2_to_eventwise_L1_transfer
    P A (fun j ω => M j ω) (fun ω => L ω)
    (fun j => (Lp.memLp (M j))) (Lp.memLp L) hL2
