-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB202_choose_simultaneous_good_stopped_clipping_level
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:16:04.008177+00:00
-- url     : https://prove2.me/submissions/fcddf977-6066-4f05-a4d0-03d38df128ce

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB201_original_postpayment_random_horizon_ae_spatial_levels_null
import Theorems.Thm_AvramDividend_Classical_avram_gbB193_select_level_avoiding_countable_null_occupations
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- One good level works across all countably many original stopping horizons. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ → ℕ) (ρ : ℕ → Ω → ℝ≥0)
    (a b : ℝ) (hab : a < b) :
    ∃ y : ℝ, y ∈ Ioo a b ∧
      ∀ k : ℕ, ∀ᵐ ω ∂P,
        volume {t : ℝ |
          0 < t ∧ t < ((n k : ℕ) : ℝ) ∧
          t < (ρ k ω : ℝ) ∧
          x + X.X (Real.toNNReal t) ω -
            rightLimit D (Real.toNNReal t) ω = y} = 0 := by
  let S : ℕ → Set ℝ := fun k =>
    {y : ℝ | ¬ ∀ᵐ ω ∂P,
      volume {t : ℝ |
        0 < t ∧ t < ((n k : ℕ) : ℝ) ∧
        t < (ρ k ω : ℝ) ∧
        x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω = y} = 0}
  have hS (k : ℕ) : (volume : Measure ℝ) (S k) = 0 := by
    have hk :=
      avram_gbB201_original_postpayment_random_horizon_ae_spatial_levels_null
        X x D hD (n k) (ρ k)
    exact (ae_iff).mp hk
  obtain ⟨y, hy, hyS⟩ :=
    avram_gbB193_select_level_avoiding_countable_null_occupations
      S hS a b hab
  refine ⟨y, hy, ?_⟩
  intro k
  exact not_not.mp (hyS k)

