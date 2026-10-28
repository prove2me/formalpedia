-- Prove2me | solution 5 for AvramDividend.Classical.bounded_variation_two_sided_exit_before_ruin_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:55:28.070876+00:00
-- url     : https://prove2.me/submissions/5a61775d-ac4a-4038-b22c-aadb95926834
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_bounded_variation_stopped_scale_balance

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
  -- Principal route: Proved positivity (59531c77) plus the exact BV-branch
  -- stopped balance (Open 2bb529c8, the authoritative decomposition child of
  -- this target) after unfolding the TwoSidedExit wrappers; close by ENNReal
  -- division algebra.
  have hWa : 0 < W a :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_standing
      X hX q hq W hW a ha
  have hInline :
      twoSidedExitExpectation X q a x =
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) := by
    unfold twoSidedExitExpectation twoSidedExitUpTime twoSidedExitDownTime
    rfl
  have hBalInline :
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x) :=
    AvramDividend.Classical.bounded_variation_stopped_scale_balance
      X hX q hq W hW hBV a x ha hx0 hxa
  have hBalance :
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x) := by
    rw [hInline]
    exact hBalInline
  have hD0 : ENNReal.ofReal (W a) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hWa)
  have hDtop : ENNReal.ofReal (W a) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hdiv :
      twoSidedExitExpectation X q a x =
        ENNReal.ofReal (W x) / ENNReal.ofReal (W a) := by
    calc
      twoSidedExitExpectation X q a x =
          (twoSidedExitExpectation X q a x * ENNReal.ofReal (W a)) /
            ENNReal.ofReal (W a) := by
        symm
        exact ENNReal.mul_div_cancel_right hD0 hDtop
      _ = ENNReal.ofReal (W x) / ENNReal.ofReal (W a) := by
        rw [hBalance]
  rw [hdiv]
  exact (ENNReal.ofReal_div_of_pos (x := W x) hWa).symm
