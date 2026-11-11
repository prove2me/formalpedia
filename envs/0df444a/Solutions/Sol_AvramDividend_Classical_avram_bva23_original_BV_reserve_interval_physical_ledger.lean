-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva23_original_BV_reserve_interval_physical_ledger
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:37:08.153703+00:00
-- url     : https://prove2.me/submissions/804a9f1e-3671-45e0-88b3-71248646fb87

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva22_original_BV_interval_physical_jump_drift_ledger
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
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
    (hBV : X.BoundedVariation) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ≥0, a ≤ b →
      riskProcess X x D b ω - riskProcess X x D a ω =
        ((b : ℝ) - (a : ℝ)) * X.drift -
          (∑' u : ℝ≥0, if a < u ∧ u ≤ b then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) -
          (D b ω - D a ω) := by
  have hpath := avram_bva22_original_BV_interval_physical_jump_drift_ledger X hX hBV
  filter_upwards [hpath] with ω hω
  intro a b hab
  have h := hω a b hab
  change (x + X.X b ω - D b ω) - (x + X.X a ω - D a ω) =
      ((b : ℝ) - (a : ℝ)) * X.drift -
        (∑' u : ℝ≥0, if a < u ∧ u ≤ b then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) -
        (D b ω - D a ω)
  linear_combination h
