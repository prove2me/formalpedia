-- Prove2me | solution 19 for AvramDividend.Classical.barrier_strategy_value
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T15:57:26.874181+00:00
-- url     : https://prove2.me/submissions/b161ca46-c82c-439f-a32d-74c84a2331c8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Continuation for AvramDividend.Classical.barrier_strategy_value [5eb63c8f]
-- Mission 1300fbe7, revision 0df444a360eaa60ab8c11dca51a86af692955474.
-- Route: killed-exit factor 8fc83520 x boundary scale-ratio a8d4c941,
-- stopped-exit identity 09663d0d, positivity 4052a131, ofReal_div algebra.
-- All four children remain Open: expected SKETCH_ACCEPTED, not a proved milestone.
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_killed_exit_mul_supValue
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_scale_ratio
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_stopped_scale_identity
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos

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
  have hder : 0 < deriv W a :=
    AvramDividend.Classical.scaleDeriv_pos X hX q hq W hW a ha
  let killedExit := ∫⁻ ω,
    if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
      ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
    else 0 ∂P
  have hfactor :
      dividendValue X q x (barrierStrategy X x a) =
        killedExit * barrierSupValue X a q := by
    change dividendValue X q x (barrierStrategy X x a) =
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) * barrierSupValue X a q
    exact AvramDividend.Classical.barrierStrategy_value_eq_killed_exit_mul_supValue
      X hX q hq a x ha hx0 hxa
  have hexit : killedExit * ENNReal.ofReal (W a) = ENNReal.ofReal (W x) := by
    change (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * ENNReal.ofReal (W a) = ENNReal.ofReal (W x)
    exact AvramDividend.Classical.two_sided_exit_stopped_scale_identity
      X hX q hq W hW a x ha hx0 hxa
  calc
    dividendValue X q x (barrierStrategy X x a) =
        killedExit * ENNReal.ofReal (W a / deriv W a) := by
      rw [hfactor]
      rw [AvramDividend.Classical.barrierSupValue_eq_scale_ratio
        X hX q hq W hW a ha]
    _ = killedExit * (ENNReal.ofReal (W a) / ENNReal.ofReal (deriv W a)) := by
      rw [ENNReal.ofReal_div_of_pos hder]
    _ = (killedExit * ENNReal.ofReal (W a)) / ENNReal.ofReal (deriv W a) := by
      rw [← mul_div_assoc]
    _ = ENNReal.ofReal (W x) / ENNReal.ofReal (deriv W a) := by
      rw [hexit]
    _ = ENNReal.ofReal (W x / deriv W a) :=
      (ENNReal.ofReal_div_of_pos hder).symm
