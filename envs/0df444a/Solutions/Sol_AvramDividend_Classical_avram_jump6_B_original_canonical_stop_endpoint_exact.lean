-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_canonical_stop_endpoint_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:25:51.457331+00:00
-- url     : https://prove2.me/submissions/c67d1312-1aec-498b-b803-fb14748b34a8

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
    ∀ k j ω, min (u j (m j)) (σ k ω) = σ k ω := by
  dsimp
  have hb :=
    avram_f16_original_physical_sigma_clock_le_finite_horizon
      X x D N τ hτeq σ hσle
  intro k j ω
  have hpos : (((j + 1 : ℕ) : ℝ≥0) ≠ 0) := by positivity
  have htop : (((N + 1) * (j + 1) : ℕ) : ℝ≥0) /
      ((j + 1 : ℕ) : ℝ≥0) = (N + 1 : ℝ≥0) := by
    push_cast
    field_simp
  rw [htop]
  exact min_eq_right (le_trans (hb k ω) (by exact_mod_cast Nat.le_succ N))
