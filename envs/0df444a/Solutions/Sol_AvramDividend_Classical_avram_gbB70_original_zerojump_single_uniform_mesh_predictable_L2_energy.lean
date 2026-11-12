-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB70_original_zerojump_single_uniform_mesh_predictable_L2_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:52:34.661258+00:00
-- url     : https://prove2.me/submissions/67546b92-be84-415a-b25a-df6391365f21

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_gbB72_original_zerojump_uniform_single_cell_diagonal_variance
import Theorems.Thm_AvramDividend_Classical_avram_gbB73_original_zerojump_uniform_finite_sum_orthogonality
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n N : ℕ) (hn : 0 < n) (hN : 0 < N)
    (H : ℕ → Ω → ℝ)
    (hAdapt : ∀ i : ℕ,
      Measurable[𝓕.rightCont
        ((i : ℝ≥0) * ((n : ℝ≥0) / (N : ℝ≥0)))] (H i))
    (hBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ i ω, |H i ω| ≤ B) :
      let Δ : ℝ≥0 := (n : ℝ≥0) / (N : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      let L : Ω → ℝ := fun ω =>
        (Finset.range N).sum (fun i =>
          H i ω * (X.X (s i + Δ) ω - X.X (s i) ω -
            (Δ : ℝ) * X.c))
      0 ≤ (∫ ω, (L ω) ^ 2 ∂P) ∧
        (∫ ω, (L ω) ^ 2 ∂P) ≤
          X.σ ^ 2 * ((n : ℝ) / (N : ℝ)) *
            (Finset.range N).sum (fun i =>
              ∫ ω, (H i ω) ^ 2 ∂P) := by
  intro Δ s L
  have hDiag : ∀ i : ℕ,
      (∫ ω, (H i ω * (X.X (s i + Δ) ω -
        X.X (s i) ω - (Δ : ℝ) * X.c)) ^ 2 ∂P) =
      (∫ ω, (H i ω) ^ 2 ∂P) * ((Δ : ℝ) * X.σ ^ 2) := by
    simpa only [Δ, s] using
      (avram_gbB72_original_zerojump_uniform_single_cell_diagonal_variance
        X hν n N hn hN H hAdapt hBound)
  have hOrth : (∫ ω, (L ω) ^ 2 ∂P) =
      (Finset.range N).sum (fun i =>
        ∫ ω, (H i ω * (X.X (s i + Δ) ω -
          X.X (s i) ω - (Δ : ℝ) * X.c)) ^ 2 ∂P) := by
    simpa only [Δ, s, L] using
      (avram_gbB73_original_zerojump_uniform_finite_sum_orthogonality
        X hν n N hn hN H hAdapt hBound)
  have hcoe : (Δ : ℝ) = (n : ℝ) / (N : ℝ) := by
    simp [Δ]
  refine ⟨integral_nonneg (fun ω => sq_nonneg (L ω)), ?_⟩
  have hExact : (∫ ω, (L ω) ^ 2 ∂P) =
      X.σ ^ 2 * ((n : ℝ) / (N : ℝ)) *
        (Finset.range N).sum (fun i =>
          ∫ ω, (H i ω) ^ 2 ∂P) := by
    calc
      _ = (Finset.range N).sum (fun i =>
          ∫ ω, (H i ω * (X.X (s i + Δ) ω -
            X.X (s i) ω - (Δ : ℝ) * X.c)) ^ 2 ∂P) := hOrth
      _ = (Finset.range N).sum (fun i =>
          (∫ ω, (H i ω) ^ 2 ∂P) * ((Δ : ℝ) * X.σ ^ 2)) := by
            simp_rw [hDiag]
      _ = X.σ ^ 2 * ((n : ℝ) / (N : ℝ)) *
          (Finset.range N).sum (fun i =>
            ∫ ω, (H i ω) ^ 2 ∂P) := by
            rw [← Finset.sum_mul]
            rw [hcoe]
            ring
  exact le_of_eq hExact
