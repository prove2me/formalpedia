-- Prove2me | solution 22 for AvramDividend.Classical.two_sided_exit_before_ruin_integral_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:38:48.615742+00:00
-- url     : https://prove2.me/submissions/61cfc2f2-dd51-41d1-9f59-7e27bca994f2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
  -- Mission-closed case split: bounded variation uses Proved/Open 494 named
  -- expectation; unbounded variation uses in-mission aed50a34 product form.
  -- Both children are in-mission Opens; off-mission 09663d0d is not cited.
  by_cases hBV : X.BoundedVariation
  · -- Bounded-variation leg: named expectation equals the raw integral by
    -- unfolding twoSidedExitUpTime/DownTime (both are the raw iInf forms).
    have h494 := AvramDividend.Classical.bounded_variation_two_sided_exit_before_ruin_identity
      X hX q hq W hW hBV a x ha hx0 hxa
    have hUnfold : twoSidedExitExpectation X q a x
        = (∫⁻ ω,
          if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
              (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
            ENNReal.ofReal
              (Real.exp (-(q * ENNReal.toReal
                (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
          else 0 ∂P) := by
      unfold twoSidedExitExpectation twoSidedExitUpTime twoSidedExitDownTime; rfl
    rw [← hUnfold]
    exact h494
  · -- Unbounded leg: product form divided by the positive barrier normaliser.
    have hProd := AvramDividend.Classical.chat04_unbounded_two_sided_exit_stopped_scale_identity
      X q hq W hW hBV a x ha hx0 hxa
    have hWa : 0 < W a := scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
    have hWa0 : ENNReal.ofReal (W a) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hWa)
    have hWaTop : ENNReal.ofReal (W a) ≠ ⊤ := ENNReal.ofReal_ne_top
    -- Remote-verified signature at 0df444a3 (private probe dd736e1c):
    -- ENNReal.ofReal_div_of_pos : ∀ {x y}, 0 < y → ofReal (x / y) = ofReal x / ofReal y.
    -- Single denominator-positivity argument; no numerator hypothesis needed.
    have hDiv : ENNReal.ofReal (W x / W a)
        = ENNReal.ofReal (W x) / ENNReal.ofReal (W a) :=
      ENNReal.ofReal_div_of_pos hWa
    rw [hDiv, ENNReal.eq_div_iff hWa0 hWaTop]
    exact (mul_comm _ _).trans hProd
