-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB77_original_zerojump_uniform_bilinear_grid_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:13:14.96535+00:00
-- url     : https://prove2.me/submissions/f75879de-6a11-4b0a-81a9-a66b4daf5dc4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB79_original_uniform_bilinear_offdiagonal
import Theorems.Thm_AvramDividend_Classical_avram_gbB80_original_uniform_single_cell_bilinear
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n N : ℕ) (hn : 0 < n) (hN : 0 < N)
    (H J : ℕ → Ω → ℝ)
    (hHAdapt : ∀ (i : ℕ), Measurable[𝓕.rightCont
      ((i : ℝ≥0) * ((n : ℝ≥0) / (N : ℝ≥0)))] (H i))
    (hJAdapt : ∀ (i : ℕ), Measurable[𝓕.rightCont
      ((i : ℝ≥0) * ((n : ℝ≥0) / (N : ℝ≥0)))] (J i))
    (hHBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ i ω, |H i ω| ≤ B)
    (hJBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ i ω, |J i ω| ≤ B) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / (N : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let L : (ℕ → Ω → ℝ) → Ω → ℝ := fun W ω =>
      (Finset.range N).sum (fun i =>
        W i ω * (X.X (s i + Δ) ω - X.X (s i) ω -
          (Δ : ℝ) * X.c))
    (∫ ω, L H ω * L J ω ∂P) =
      ((Δ : ℝ) * X.σ ^ 2) *
        (Finset.range N).sum (fun i => ∫ ω, H i ω * J i ω ∂P) := by
  intro Δ s L
  let Z : ℕ → Ω → ℝ := fun i ω =>
    X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
  have hOrth :
      (∫ ω, L H ω * L J ω ∂P) =
        (Finset.range N).sum (fun i =>
          ∫ ω, (H i ω * Z i ω) * (J i ω * Z i ω) ∂P) := by
    simpa only [L, Z, s, Δ] using
      (avram_gbB79_original_uniform_bilinear_offdiagonal
        X hν n N hn hN H J hHAdapt hJAdapt hHBound hJBound)
  have hDiag : ∀ i : ℕ,
      (∫ ω, (H i ω * Z i ω) * (J i ω * Z i ω) ∂P) =
      ((Δ : ℝ) * X.σ ^ 2) *
        (∫ ω, H i ω * J i ω ∂P) := by
    simpa only [Z, s, Δ] using
      (avram_gbB80_original_uniform_single_cell_bilinear
        X hν n N hn hN H J hHAdapt hJAdapt hHBound hJBound)
  calc
    (∫ ω, L H ω * L J ω ∂P) =
        (Finset.range N).sum (fun i =>
          ∫ ω, (H i ω * Z i ω) * (J i ω * Z i ω) ∂P) := hOrth
    _ = (Finset.range N).sum (fun i =>
          ((Δ : ℝ) * X.σ ^ 2) *
            (∫ ω, H i ω * J i ω ∂P)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hDiag i
    _ = ((Δ : ℝ) * X.σ ^ 2) *
          (Finset.range N).sum (fun i =>
            ∫ ω, H i ω * J i ω ∂P) := by
            rw [Finset.mul_sum]
