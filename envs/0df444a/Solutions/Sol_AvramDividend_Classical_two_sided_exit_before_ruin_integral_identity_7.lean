-- Prove2me | solution 7 for AvramDividend.Classical.two_sided_exit_before_ruin_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T17:05:53.69496+00:00
-- url     : https://prove2.me/submissions/e042d347-9fc2-4040-b5ea-ab584d3be19a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_bounded_variation_two_sided_exit_before_ruin_identity
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_two_sided_exit_stopped_scale_identity
import Theorems.Thm_AvramDividend_Classical_chat04_exit_ratio_of_stopped_balance

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
  classical
  by_cases hBV : X.BoundedVariation
  · exact AvramDividend.Classical.bounded_variation_two_sided_exit_before_ruin_identity
      X hX q hq W hW hBV a x ha hx0 hxa
  · have hBalance :
        twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
          ENNReal.ofReal (W x) :=
      AvramDividend.Classical.chat04_unbounded_two_sided_exit_stopped_scale_identity
        X q hq W hW hBV a x ha hx0 hxa
    exact AvramDividend.Classical.chat04_exit_ratio_of_stopped_balance
      X hX q hq W hW a x ha hx0 hxa hBalance
