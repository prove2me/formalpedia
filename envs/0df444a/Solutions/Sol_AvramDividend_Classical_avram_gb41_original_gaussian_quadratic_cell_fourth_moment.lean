-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb41_original_gaussian_quadratic_cell_fourth_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:46:44.297185+00:00
-- url     : https://prove2.me/submissions/b8c62c57-48b2-4477-979d-0108454a5a52

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb51_sigma_zero_original_quadratic_cell_fourth
import Theorems.Thm_AvramDividend_Classical_avram_gb52_original_positive_sigma_quadratic_cell_L2
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original Gaussian squared-mesh residual follows by splitting the
vanishing and positive Gaussian coefficients. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hν : X.ν = 0) (n : ℕ) (hn : 0 < n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : ℕ) (i : ℕ), i ∈ Finset.range (m + 1) →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let R : Ω → ℝ := fun ω =>
        (X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c) ^ 2 -
          (Δ : ℝ) * X.σ ^ 2
      Integrable (fun ω => (R ω) ^ 2) P ∧
        (∫ ω, (R ω) ^ 2 ∂P) ≤ K / (((m + 1 : ℕ) : ℝ) ^ 2) := by
  have hσnn : 0 ≤ X.σ := by
    first
    | exact X.σ_nonneg
    | exact hX.σ_nonneg
    | exact X.sigma_nonneg
    | exact hX.sigma_nonneg
  rcases eq_or_lt_of_le hσnn with hzero | hpos
  · exact avram_gb51_sigma_zero_original_quadratic_cell_fourth
      X hX hν hzero.symm n hn
  · refine ⟨8 * X.σ ^ 4 * (n : ℝ) ^ 2, ?_, ?_⟩
    · exact mul_nonneg
        (mul_nonneg (by norm_num) (pow_nonneg (le_of_lt hpos) 4))
        (sq_nonneg _)
    intro m i hi
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let R : Ω → ℝ := fun ω =>
      (X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c) ^ 2 -
        (Δ : ℝ) * X.σ ^ 2
    change Integrable (fun ω => (R ω) ^ 2) P ∧
      (∫ ω, (R ω) ^ 2 ∂P) ≤
        (8 * X.σ ^ 4 * (n : ℝ) ^ 2) /
          (((m + 1 : ℕ) : ℝ) ^ 2)
    have hcell : Integrable (fun ω => (R ω) ^ 2) P ∧
        (∫ ω, (R ω) ^ 2 ∂P) ≤
          8 * X.σ ^ 4 * (Δ : ℝ) ^ 2 := by
      exact avram_gb52_original_positive_sigma_quadratic_cell_L2
        X hν hpos s Δ
    refine ⟨hcell.1, le_trans hcell.2 ?_⟩
    apply le_of_eq
    dsimp [Δ]
    simp only [NNReal.coe_div, NNReal.coe_natCast]
    ring
