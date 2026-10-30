-- Prove2me | solution 9 for AvramDividend.Classical.bounded_variation_two_sided_exit_before_ruin_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T23:36:46.474991+00:00
-- url     : https://prove2.me/submissions/d05936c5-2d59-4a0b-bc5a-bbfaf4beef06

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_bounded_variation_stopped_scale_balance
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    twoSidedExitExpectation X q a x = ENNReal.ofReal (W x / W a) := by
  have hpos : 0 < W a :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hWa0 : ENNReal.ofReal (W a) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hpos
  have hWatop : ENNReal.ofReal (W a) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hBal : (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) :=
    AvramDividend.Classical.bounded_variation_stopped_scale_balance X hX q hq W hW hBV a x ha hx0 hxa
  have hEI : twoSidedExitExpectation X q a x =
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) := rfl
  rw [hEI, ENNReal.ofReal_div_of_pos hpos, ENNReal.eq_div_iff hWa0 hWatop, mul_comm]
  exact hBal
