-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB39_original_postpayment_gaussian_exact_level_occupation_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:51:13.155917+00:00
-- url     : https://prove2.me/submissions/419b32ec-7fd3-40c5-97ba-257d0d1ecb6b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB141_original_gaussian_fixed_level_shrinking_band_occupation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω = b} = 0 := by
  have hshr := avram_gbB141_original_gaussian_fixed_level_shrinking_band_occupation
    X hBV hν x b D hD n ρ
  filter_upwards [hshr] with ω hlim
  let S : Set ℝ := {t : ℝ |
    0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
      x + X.X (Real.toNNReal t) ω -
        rightLimit D (Real.toNNReal t) ω = b}
  have hbound (k : ℕ) :
      volume S ≤
        volume {t : ℝ |
          0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
          abs (x + X.X (Real.toNNReal t) ω -
            rightLimit D (Real.toNNReal t) ω - b) <
              (1 : ℝ) / ((k : ℝ) + 1)} := by
    apply measure_mono
    intro t ht
    rcases ht with ⟨ht0, htn, htρ, heq⟩
    refine ⟨ht0, htn, htρ, ?_⟩
    simp only [heq, sub_self, abs_zero]
    positivity
  have hz : volume S ≤ (0 : ℝ≥0∞) :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  exact le_antisymm hz bot_le
