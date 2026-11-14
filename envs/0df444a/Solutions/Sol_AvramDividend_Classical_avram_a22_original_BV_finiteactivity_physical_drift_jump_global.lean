-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_BV_finiteactivity_physical_drift_jump_global
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:51:23.066721+00:00
-- url     : https://prove2.me/submissions/e8f8b1b6-429d-4b3d-b91f-b63b12101f72

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original global BV drift and jump decomposition follows from exact vanishing of its residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (t : ℝ) * X.drift - X.X t ω =
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by
  have hSource := avram_redux11_original_BV_raw_removed_residual_zero_ae
    X hX hBV
  filter_upwards [hSource] with ω hω
  intro t
  have ht := hω t
  linarith
