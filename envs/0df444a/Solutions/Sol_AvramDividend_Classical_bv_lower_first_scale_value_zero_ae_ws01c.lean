-- Prove2me | solution 1 for AvramDividend.Classical.bv_lower_first_scale_value_zero_ae_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:18:45.84134+00:00
-- url     : https://prove2.me/submissions/bd8ff05b-5194-4f27-be0f-7e9e38a4152d

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_strict_lower_exit_undershoot_ae_ws01c

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-! The original BV lower-first terminal q-scale vanishes without discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    ∀ᵐ ω ∂P,
      twoSidedExitDownTime X (-x) ω <
        twoSidedExitUpTime X (a - x) ω →
      W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω) = 0 := by
  have hNegative :=
    bv_strict_lower_exit_undershoot_ae_ws01c
      X hX q hq W hW hBV a x ha hx0 hxa
  filter_upwards [hNegative] with ω hlt
  intro hLower
  exact hW.1 _ (hlt hLower)
