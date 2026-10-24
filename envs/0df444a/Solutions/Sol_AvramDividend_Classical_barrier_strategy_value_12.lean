-- Prove2me | solution 12 for AvramDividend.Classical.barrier_strategy_value
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:16:34.786131+00:00
-- url     : https://prove2.me/submissions/c04a1344-cfd5-44be-a938-f376cf2e184c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_killed_exit_mul_supValue
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_integral_identity
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_scale_ratio
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_ennreal_scale_ratio_cancel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) = ENNReal.ofReal (W x / deriv W a) := by
  have hWa : 0 < W a :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hderiv : 0 < deriv W a := scaleDeriv_pos X hX q hq W hW a ha
  calc
    dividendValue X q x (barrierStrategy X x a) =
        (∫⁻ ω,
          if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
              (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
            ENNReal.ofReal
              (Real.exp (-(q * ENNReal.toReal
                (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
          else 0 ∂P) * barrierSupValue X a q :=
      barrierStrategy_value_eq_killed_exit_mul_supValue X hX q hq a x ha hx0 hxa
    _ = ENNReal.ofReal (W x / W a) * ENNReal.ofReal (W a / deriv W a) := by
      rw [two_sided_exit_before_ruin_integral_identity X hX q hq W hW a x ha hx0 hxa,
        barrierSupValue_eq_scale_ratio X hX q hq W hW a ha]
    _ = ENNReal.ofReal (W x / deriv W a) :=
      ennreal_scale_ratio_cancel (W x) (W a) (deriv W a)
        (hW.2.1 x hx0) hWa hderiv
