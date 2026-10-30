-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_bv_lower_first_capped_terminal_scale_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:58:08.812035+00:00
-- url     : https://prove2.me/submissions/f643d02b-25d2-4c08-bacc-5e77efa35498

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_bv_strict_lower_exit_undershoot_ae_ws01c
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- On genuine BV lower-first ruin before the cap, the discounted stopped scale vanishes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a-x) ω →
      (twoSidedExitDownTime X (-x) ω).toNNReal ≤ T →
      Real.exp (-(q * ((min
        (min (twoSidedExitUpTime X (a-x) ω)
          (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
      W (x + X.X (min
        (min (twoSidedExitUpTime X (a-x) ω)
          (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω) = 0 := by
  have hUndershoot := bv_strict_lower_exit_undershoot_ae_ws01c
    X hX q hq W hW hBV a x ha hx0 hxa
  filter_upwards [hUndershoot] with ω hω
  intro hDown hCap
  have hmin : min (twoSidedExitUpTime X (a-x) ω)
      (twoSidedExitDownTime X (-x) ω) =
      twoSidedExitDownTime X (-x) ω := min_eq_right hDown.le
  have hneg := hω hDown
  have hzero : W (x + X.X
      (twoSidedExitDownTime X (-x) ω).toNNReal ω) = 0 :=
    hW.1 _ hneg
  simp only [hmin, min_eq_left hCap, hzero, mul_zero]
