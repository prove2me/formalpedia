-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB141_original_gaussian_fixed_level_shrinking_band_occupation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:23:41.620581+00:00
-- url     : https://prove2.me/submissions/530935c4-2705-4a15-9167-f22bc13c6cc0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_avram_gbB168_ennreal_nonnegative_squeeze_zero
import Theorems.Thm_AvramDividend_Classical_avram_gbB169_original_gaussian_finite_localtime_linear_band_mass_bound
import Theorems.Thm_avram_gbB170_ennreal_shrinking_band_rate_tendsto_zero
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
      Tendsto (fun k : ℕ =>
        volume {t : ℝ |
          0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
          abs (x + X.X (Real.toNNReal t) ω -
            rightLimit D (Real.toNNReal t) ω - b) <
              (1 : ℝ) / ((k : ℝ) + 1)})
        atTop (𝓝 (0 : ℝ≥0∞)) := by
  have hlocal :=
    avram_gbB169_original_gaussian_finite_localtime_linear_band_mass_bound
      X hBV hν x b D hD n ρ
  filter_upwards [hlocal] with ω hω
  rcases hω with ⟨L, hL⟩
  exact avram_gbB168_ennreal_nonnegative_squeeze_zero
    (fun k : ℕ =>
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        abs (x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω - b) <
            (1 : ℝ) / ((k : ℝ) + 1)})
    (fun k : ℕ => ENNReal.ofReal ((L : ℝ) / ((k : ℝ) + 1)))
    (avram_gbB170_ennreal_shrinking_band_rate_tendsto_zero L) hL
