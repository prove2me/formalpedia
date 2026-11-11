-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva22_original_finite_activity_standing_exact_drift_jump_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:43:25.92664+00:00
-- url     : https://prove2.me/submissions/10d12612-e407-42b4-bee9-2052792a7893

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      (t : ℝ) * X.drift - X.X t ω =
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by
  filter_upwards
    [avram_redux11_original_BV_raw_removed_residual_zero_ae X hX hBV]
    with ω hω
  intro t ht
  exact sub_eq_zero.mp (hω t)
