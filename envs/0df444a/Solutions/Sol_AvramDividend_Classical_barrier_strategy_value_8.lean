-- Prove2me | solution 8 for AvramDividend.Classical.barrier_strategy_value
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:51:40.610253+00:00
-- url     : https://prove2.me/submissions/93889071-47a7-40d6-9081-9527f2fd0921
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_killed_exit_mul_supValue
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_identity
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_scale_ratio
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_ennreal_scale_ratio_cancel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) = ENNReal.ofReal (W x / deriv W a) := by
  let C : ℝ≥0∞ :=
    ∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂P
  have hfactor :
      dividendValue X q x (barrierStrategy X x a) = C * barrierSupValue X a q := by
    simpa only [C, twoSidedExitUpTime] using
      (AvramDividend.Classical.barrierStrategy_value_eq_killed_exit_mul_supValue
        X hX q hq a x ha hx0 hxa)
  have hWa : 0 < W a :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_standing
      X hX q hq W hW a ha
  have hC : C = ENNReal.ofReal (W x / W a) := by
    change twoSidedExitExpectation X q a x = _
    exact AvramDividend.Classical.two_sided_exit_before_ruin_identity
      X hX q hq W hW a x ha hx0 hxa
  have hboundary :
      barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a) :=
    AvramDividend.Classical.barrierSupValue_eq_scale_ratio X hX q hq W hW a ha
  have hWx : 0 ≤ W x := hW.2.1 x hx0
  have hratio :
      ENNReal.ofReal (W x / W a) * ENNReal.ofReal (W a / deriv W a) =
        ENNReal.ofReal (W x / deriv W a) := by
    by_cases hd : 0 < deriv W a
    · exact AvramDividend.Classical.ennreal_scale_ratio_cancel
        (W x) (W a) (deriv W a) hWx hWa hd
    · have hdn : deriv W a ≤ 0 := le_of_not_gt hd
      have hboundaryZero : ENNReal.ofReal (W a / deriv W a) = 0 := by
        apply ENNReal.ofReal_eq_zero.mpr
        exact div_nonpos_of_nonneg_of_nonpos hWa.le hdn
      have htargetZero : ENNReal.ofReal (W x / deriv W a) = 0 := by
        apply ENNReal.ofReal_eq_zero.mpr
        exact div_nonpos_of_nonneg_of_nonpos hWx hdn
      simp [hboundaryZero, htargetZero]
  calc
    dividendValue X q x (barrierStrategy X x a) =
        C * barrierSupValue X a q := hfactor
    _ = ENNReal.ofReal (W x / deriv W a) := by
      rw [hC, hboundary]
      exact hratio
