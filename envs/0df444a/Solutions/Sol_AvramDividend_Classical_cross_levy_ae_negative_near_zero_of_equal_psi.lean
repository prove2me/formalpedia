-- Prove2me | solution 1 for AvramDividend.Classical.cross_levy_ae_negative_near_zero_of_equal_psi
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:51:48.164311+00:00
-- url     : https://prove2.me/submissions/fab0be21-24c0-4c1e-bdce-97417c4f06e8

import Theorems.Thm_AvramDividend_Classical_cross_levy_ae_negative_grid_of_equal_psi
import Theorems.Thm_AvramDividend_Classical_levy_negative_before_horizon_iff_dense_grid
import Mathlib.MeasureTheory.OuterMeasure.AE

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hψ : ∀ θ : ℝ, 0 < θ → X.ψ θ = Y.ψ θ)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (hRegY : ∀ᵐ ω ∂P₂, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ Y.X s ω < 0) :
    ∀ᵐ ω ∂P₁, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0 := by
  have hGridY : ∀ᵐ ω ∂P₂, ∀ n : ℕ, ∃ m : ℕ,
      times m < horizons n ∧ Y.X (times m) ω < 0 := by
    filter_upwards [hRegY] with ω hω n
    exact (AvramDividend.Classical.levy_negative_before_horizon_iff_dense_grid
      Y times hdense ω (horizons n)).mp (hω _ (hpos n))
  have hX := AvramDividend.Classical.cross_levy_ae_negative_grid_of_equal_psi X Y hψ times horizons hGridY
  filter_upwards [hX] with ω hω ε hε
  obtain ⟨n, hn⟩ := hcofinal ε hε
  obtain ⟨m, hm1, hm2⟩ := hω n
  exact ⟨times m, lt_of_lt_of_le hm1 hn, hm2⟩
