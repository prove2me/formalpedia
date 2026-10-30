-- Prove2me | solution 6 for AvramDividend.Classical.bounded_variation_two_sided_exit_before_ruin_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:45:30.540496+00:00
-- url     : https://prove2.me/submissions/060b0fcd-46fe-49ba-9bd8-1bd482086550

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
  -- Principal route: reduction to the in-mission Open balance 2bb529c8
  -- (product form of the stopped scale identity) plus ENNReal division
  -- algebra; Proved positivity 59531c77 supplies the division side
  -- conditions. Reduction with an Open import may return SKETCH_ACCEPTED.
  have hProd := AvramDividend.Classical.bounded_variation_stopped_scale_balance
    X hX q hq W hW hBV a x ha hx0 hxa
  have hWa : 0 < W a := scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hWx : 0 ≤ W x := hW.2.1 x hx0
  have hUnfold : twoSidedExitExpectation X q a x
      = (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) := by
    unfold twoSidedExitExpectation twoSidedExitUpTime twoSidedExitDownTime
    rfl
  -- E02 repair: `ENNReal.ofReal_ne_zero` does not exist at the pinned
  -- revision; pinned `ENNReal.ofReal_pos : 0 < ofReal p ↔ 0 < p`, so
  -- positivity gives nonzeroness via core `ne_of_gt`.
  have hWa0 : ENNReal.ofReal (W a) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hWa)
  have hWaTop : ENNReal.ofReal (W a) ≠ ⊤ := ENNReal.ofReal_ne_top
  -- E03 repair: pinned `ENNReal.ofReal_div_of_pos` takes only the
  -- denominator positivity (`∀ {x y}, 0 < y → ofReal (x / y) =
  -- ofReal x / ofReal y`); no numerator hypothesis is needed or accepted.
  have hDiv : ENNReal.ofReal (W x / W a)
      = ENNReal.ofReal (W x) / ENNReal.ofReal (W a) :=
    ENNReal.ofReal_div_of_pos hWa
  have hQuot : (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P)
      = ENNReal.ofReal (W x) / ENNReal.ofReal (W a) := by
    rw [ENNReal.eq_div_iff hWa0 hWaTop]
    -- E04 repair: the `eq_div_iff` normal form here is
    -- `ofReal (W a) * integral = ofReal (W x)` (denominator on the left),
    -- while hProd has `integral * ofReal (W a)`; close by commutativity.
    rw [mul_comm (ENNReal.ofReal (W a))]
    exact hProd
  rw [hUnfold, hQuot, hDiv]
