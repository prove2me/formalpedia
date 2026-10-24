-- Prove2me | solution 10 for AvramDividend.Classical.barrier_strategy_value
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:44:02.215656+00:00
-- url     : https://prove2.me/submissions/284979a8-7546-44b6-bafe-fb793c83e571
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_killed_exit_integral_mul_boundaryValue
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_integral_identity
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_scale_ratio
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos
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
  have hmarkov :=
    AvramDividend.Classical.barrierStrategy_value_eq_killed_exit_integral_mul_boundaryValue
      X hX q hq a x ha hx0 hxa
  have hexit : (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W x / W a) :=
    AvramDividend.Classical.two_sided_exit_before_ruin_integral_identity
      X hX q hq W hW a x ha hx0 hxa
  have hbridge : dividendValue X q a (barrierStrategy X a a) = barrierSupValue X a q :=
    AvramDividend.Classical.barrierValue_self_eq_barrierSupValue X q a
  have hWa : 0 < W a :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_standing
      X hX q hq W hW a ha
  have hboundary :
      barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a) :=
    AvramDividend.Classical.barrierSupValue_eq_scale_ratio X hX q hq W hW a ha
  have hderiv : 0 < deriv W a :=
    AvramDividend.Classical.scaleDeriv_pos X hX q hq W hW a ha
  calc dividendValue X q x (barrierStrategy X x a)
        = (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * dividendValue X q a (barrierStrategy X a a) := hmarkov
    _ = (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * barrierSupValue X a q := by rw [hbridge]
    _ = ENNReal.ofReal (W x / W a) * barrierSupValue X a q := by rw [hexit]
    _ = ENNReal.ofReal (W x / deriv W a) := by
      rw [hboundary]
      exact AvramDividend.Classical.ennreal_scale_ratio_cancel
        (W x) (W a) (deriv W a) (hW.2.1 x hx0) hWa hderiv
