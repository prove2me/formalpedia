-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB100_original_gaussian_fixed_level_occupation_null
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T09:45:17.497636+00:00
-- url     : https://prove2.me/submissions/be5b2017-c0bf-4ab2-9d21-2c730c0fe1c6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB140_zero_level_from_shrinking_band_occupation
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
  have hBand :=
    avram_gbB141_original_gaussian_fixed_level_shrinking_band_occupation
      X hBV hν x b D hD n ρ
  filter_upwards [hBand] with ω hω
  let A : Set ℝ := {t | 0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
    x + X.X (Real.toNNReal t) ω - rightLimit D (Real.toNNReal t) ω = b}
  let S : ℕ → Set ℝ := fun k => {t |
    0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
    abs (x + X.X (Real.toNNReal t) ω -
      rightLimit D (Real.toNNReal t) ω - b) < (1 : ℝ) / ((k : ℝ) + 1)}
  change volume A = 0
  apply avram_gbB140_zero_level_from_shrinking_band_occupation
    (volume A) (fun k => volume (S k))
  · intro k
    apply measure_mono
    intro t ht
    rcases ht with ⟨h1,h2,h3,h4⟩
    exact ⟨h1,h2,h3,by rw [h4,sub_self,abs_zero]; positivity⟩
  · simpa only [S] using hω
