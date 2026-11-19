-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_refining_physical_grid_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T16:25:50.169933+00:00
-- url     : https://prove2.me/submissions/f2fa9a07-b3b4-486b-861b-6f467c2b79f8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_physical_sigma_clock_le_finite_horizon
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
    (∀ k ω, ∀ᶠ j in atTop, σ k ω ≤ u j (m j)) := by
  dsimp
  have hb := avram_f16_original_physical_sigma_clock_le_finite_horizon
    X x D N τ hτeq σ hσle
  refine ⟨?_, ?_, ?_⟩
  · intro j a b hab
    dsimp
    gcongr
  · intro j
    simp
  · intro k ω
    apply Filter.Eventually.of_forall
    intro j
    have hpos : (((j + 1 : ℕ) : ℝ≥0) ≠ 0) := by positivity
    have htop : (((N + 1) * (j + 1) : ℕ) : ℝ≥0) /
        ((j + 1 : ℕ) : ℝ≥0) = (N + 1 : ℝ≥0) := by
      push_cast
      field_simp
    rw [htop]
    exact le_trans (hb k ω) (by exact_mod_cast Nat.le_succ N)
