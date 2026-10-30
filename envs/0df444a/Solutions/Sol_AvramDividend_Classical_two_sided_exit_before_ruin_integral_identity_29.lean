-- Prove2me | solution 29 for AvramDividend.Classical.two_sided_exit_before_ruin_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:05:14.079827+00:00
-- url     : https://prove2.me/submissions/0ee04e9f-784a-4b36-9f26-dc74df213262

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_bounded_variation_two_sided_exit_before_ruin_identity
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_two_sided_exit_stopped_scale_identity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) =
      ENNReal.ofReal (W x / W a) := by
  by_cases hBV : X.BoundedVariation
  · -- Bounded-variation branch: fold the raw lintegral to the
    -- twoSidedExitExpectation definition, then apply the in-frontier BV
    -- identity 494dbcd1 (Standing + BV, exact same binders/conclusion).
    have hfold :
        (∫⁻ ω,
          if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
              (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
            ENNReal.ofReal
              (Real.exp (-(q * ENNReal.toReal
                (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
          else 0 ∂P) =
        twoSidedExitExpectation X q a x := by
      unfold twoSidedExitExpectation twoSidedExitUpTime twoSidedExitDownTime
      rfl
    rw [hfold]
    exact AvramDividend.Classical.bounded_variation_two_sided_exit_before_ruin_identity
      X hX q hq W hW hBV a x ha hx0 hxa
  · -- Unbounded-variation branch: in-frontier stopped identity aed50a34
    -- (same raw integral, extra hnbv hypothesis discharged by hBV) gives
    -- I * ofReal (W a) = ofReal (W x); divide by Proved positivity 59531c77.
    have hWpos : 0 < W a :=
      AvramDividend.Classical.scaleFunction_strict_pos_of_standing
        X hX q hq W hW a ha
    have hden0 : ENNReal.ofReal (W a) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr hWpos)
    have hdenTop : ENNReal.ofReal (W a) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hbal :
        (∫⁻ ω,
          if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
              (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
            ENNReal.ofReal
              (Real.exp (-(q * ENNReal.toReal
                (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
          else 0 ∂P) * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x) :=
      AvramDividend.Classical.chat04_unbounded_two_sided_exit_stopped_scale_identity
        X q hq W hW hBV a x ha hx0 hxa
    have hdiv :
        (∫⁻ ω,
          if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
              (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
            ENNReal.ofReal
              (Real.exp (-(q * ENNReal.toReal
                (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
          else 0 ∂P) =
          ENNReal.ofReal (W x) / ENNReal.ofReal (W a) := by
      calc
        (∫⁻ ω,
          if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
              (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
            ENNReal.ofReal
              (Real.exp (-(q * ENNReal.toReal
                (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
          else 0 ∂P) =
            ((∫⁻ ω,
          if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
              (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
            ENNReal.ofReal
              (Real.exp (-(q * ENNReal.toReal
                (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
          else 0 ∂P) * ENNReal.ofReal (W a)) /
              ENNReal.ofReal (W a) := by
                symm
                exact ENNReal.mul_div_cancel_right hden0 hdenTop
        _ = ENNReal.ofReal (W x) / ENNReal.ofReal (W a) := by rw [hbal]
    simpa only [ENNReal.ofReal_div_of_pos hWpos] using hdiv
