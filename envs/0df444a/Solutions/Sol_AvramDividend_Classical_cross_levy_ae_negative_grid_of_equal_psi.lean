-- Prove2me | solution 1 for AvramDividend.Classical.cross_levy_ae_negative_grid_of_equal_psi
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:43:05.661999+00:00
-- url     : https://prove2.me/submissions/78d2cc7d-375b-47aa-9711-7a51f68536c0

import Mathlib.MeasureTheory.OuterMeasure.AE
import Theorems.Thm_AvramDividend_Classical_cross_levy_path_event_law_of_equal_psi
import Theorems.Thm_AvramDividend_Classical_measurableSet_countable_schedule_negative_near_zero

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
    (hGridY : ∀ᵐ ω ∂P₂, ∀ n : ℕ, ∃ m : ℕ,
      times m < horizons n ∧ Y.X (times m) ω < 0) :
    ∀ᵐ ω ∂P₁, ∀ n : ℕ, ∃ m : ℕ,
      times m < horizons n ∧ X.X (times m) ω < 0 := by
  have hE := AvramDividend.Classical.measurableSet_countable_schedule_negative_near_zero times horizons
  have h := AvramDividend.Classical.cross_levy_path_event_law_of_equal_psi X Y hψ _ hE.compl
  rw [ae_iff] at hGridY ⊢
  have e1 : {ω : Ω₁ | ¬ ∀ n : ℕ, ∃ m : ℕ, times m < horizons n ∧ X.X (times m) ω < 0} =
      {ω : Ω₁ | (fun t : ℝ≥0 => X.X t ω) ∈ {f : ℝ≥0 → ℝ | ∀ n : ℕ, ∃ m : ℕ,
        times m < horizons n ∧ f (times m) < 0}ᶜ} := rfl
  have e2 : {ω : Ω₂ | ¬ ∀ n : ℕ, ∃ m : ℕ, times m < horizons n ∧ Y.X (times m) ω < 0} =
      {ω : Ω₂ | (fun t : ℝ≥0 => Y.X t ω) ∈ {f : ℝ≥0 → ℝ | ∀ n : ℕ, ∃ m : ℕ,
        times m < horizons n ∧ f (times m) < 0}ᶜ} := rfl
  rw [e1, h, ← e2, hGridY]
