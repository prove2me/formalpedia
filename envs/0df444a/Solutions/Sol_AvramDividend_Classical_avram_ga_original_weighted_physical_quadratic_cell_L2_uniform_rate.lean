-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_weighted_physical_quadratic_cell_L2_uniform_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:26:31.449279+00:00
-- url     : https://prove2.me/submissions/3e0a782a-18b9-44cd-8c87-1cf6cd186101

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gb41_original_gaussian_quadratic_cell_fourth_moment
import Theorems.Thm_AvramDividend_Classical_avram_ga_bounded_random_Hessian_weight_L2_integral_le
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hν : X.ν = 0) (n : ℕ) (hn : 0 < n)
    (H : ℕ → ℕ → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ m i ω, |H m i ω| ≤ K)
    (hHI : ∀ m i, i ∈ Finset.range (m + 1) →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      Integrable (fun ω => (H m i ω * ((X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c) ^ 2 -
          (Δ : ℝ) * X.σ ^ 2)) ^ 2) P) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ m i, i ∈ Finset.range (m + 1) →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      (∫ ω, (H m i ω * ((X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c) ^ 2 -
          (Δ : ℝ) * X.σ ^ 2)) ^ 2 ∂P) ≤
        J / (((m + 1 : ℕ) : ℝ) ^ 2) := by
  obtain ⟨J, hJ, hVar⟩ :=
    avram_gb41_original_gaussian_quadratic_cell_fourth_moment
      X hX hν n hn
  refine ⟨K ^ 2 * J, mul_nonneg (sq_nonneg K) hJ, ?_⟩
  intro m i hi
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  let R : Ω → ℝ := fun ω =>
    (X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c) ^ 2 -
      (Δ : ℝ) * X.σ ^ 2
  have hRInt : Integrable (fun ω => R ω ^ 2) P := (hVar m i hi).1
  have hRBound :
      (∫ ω, R ω ^ 2 ∂P) ≤ J / (((m + 1 : ℕ) : ℝ) ^ 2) :=
    (hVar m i hi).2
  have hHRInt : Integrable (fun ω => (H m i ω * R ω) ^ 2) P :=
    hHI m i hi
  have hComp := avram_ga_bounded_random_Hessian_weight_L2_integral_le
    P (H m i) R K hK (hH m i) hRInt hHRInt
  change (∫ ω, (H m i ω * R ω) ^ 2 ∂P) ≤
    K ^ 2 * J / (((m + 1 : ℕ) : ℝ) ^ 2)
  calc
    (∫ ω, (H m i ω * R ω) ^ 2 ∂P) ≤
        K ^ 2 * (∫ ω, R ω ^ 2 ∂P) := hComp
    _ ≤ K ^ 2 * (J / (((m + 1 : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hRBound (sq_nonneg K)
    _ = K ^ 2 * J / (((m + 1 : ℕ) : ℝ) ^ 2) := by ring
