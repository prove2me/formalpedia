-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB201_original_postpayment_random_horizon_ae_spatial_levels_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:13:54.550071+00:00
-- url     : https://prove2.me/submissions/ea27d1bd-ba44-4ce0-a629-ae1fe2485fc2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB189_original_postpayment_reserve_ae_spatial_levels_null_occupation
import Theorems.Thm_AvramDividend_Classical_avram_gbB195_null_unstopped_level_implies_null_stopped
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Almost-every clipping level is null even after an arbitrary time restriction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) :
    ∀ᵐ y ∂(volume : Measure ℝ), ∀ᵐ ω ∂P,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω = y} = 0 := by
  filter_upwards
    [avram_gbB189_original_postpayment_reserve_ae_spatial_levels_null_occupation
      X x D hD n] with y hy
  exact
    avram_gbB195_null_unstopped_level_implies_null_stopped
      P (fun ω t => x + X.X (Real.toNNReal t) ω -
        rightLimit D (Real.toNNReal t) ω) n y hy ρ

