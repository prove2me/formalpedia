-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_ruin_clock_stopped_compensated_path_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:27:17.01819+00:00
-- url     : https://prove2.me/submissions/cc1fe88f-5bae-494a-b022-b9f675cd61c0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original negative-jump correction cancels precisely at the
actual dividend-dependent bounded ruin clock, almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (S : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
      let J : ℝ≥0 → ℝ := fun r =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ r then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      X.X (min t τ) ω + J (min t τ) =
        ((min t τ : ℝ≥0) : ℝ) * X.drift := by
  filter_upwards [avram_redux11_original_BV_raw_removed_residual_zero_ae
    X hX hBV] with ω hω
  intro t
  dsimp only
  have h := hω (min t
    ((min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal))
  linarith [h]
