-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_physical_grid_and_ruin_clock_certificates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T16:32:26.30716+00:00
-- url     : https://prove2.me/submissions/3d75f752-6fff-4d8f-9834-ee7577df9c8a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_refining_physical_grid_cover
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_subordinate_clock_le_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (N : ℕ)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (N : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    let u : ℕ → ℕ → ℝ≥0 := fun j i =>
      (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
    let m : ℕ → ℕ := fun j => (N + 1) * (j + 1)
    (∀ j, Monotone (u j)) ∧
    (∀ j, u j 0 = 0) ∧
    (∀ k ω, ∀ᶠ j in atTop, σ k ω ≤ u j (m j)) ∧
    (∀ k ω, (σ k ω : ℝ≥0∞) ≤ ruinTime X x D ω) := by
  have hgrid :=
    avram_jump6_B_original_refining_physical_grid_cover
      X x D N τ hτeq σ hσle
  have hruin :=
    avram_jump6_B_original_subordinate_clock_le_ruin
      X x D N τ hτeq σ hσle
  dsimp at hgrid ⊢
  exact ⟨hgrid.1, hgrid.2.1, hgrid.2.2, hruin⟩
