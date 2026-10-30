-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_cstar_value_of_gaussian_or_bv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:35:41.931967+00:00
-- url     : https://prove2.me/submissions/2dd6fc0b-d1f5-4049-87e0-f320a5682d83

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_scaleDeriv_pos_of_gaussian_or_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_barrierSupValue_scale_ratio_of_gaussian_or_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
import Theorems.Thm_AvramDividend_Classical_ennreal_scale_ratio_cancel
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_zero_all_capital
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_above_value_of_boundary
import Theorems.Thm_AvramDividend_Classical_barrierValue_at_positive_barrier_eq_deriv_ratio
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_at_nonnegative_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Actual cstar reflected regulator value under Gaussian or BV regularity. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hbranch : 0 < X.σ ∨ X.BoundedVariation) :
    ∀ x : ℝ, 0 ≤ x →
      dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
        ENNReal.ofReal (vcstar W x) := by
  intro x hx
  let a : ℝ := (cstar W).toReal
  change dividendValue X q x (barrierStrategy X x a) =
    ENNReal.ofReal (barrierValue W a x)
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  by_cases hzero : a = 0
  · simpa [hzero] using
      (barrier_strategy_value_zero_all_capital X hX q hq W hW x hx)
  · have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hzero)
    have hratio : barrierSupValue X a q =
        ENNReal.ofReal (W a / deriv W a) :=
      avram_wave3_02_barrierSupValue_scale_ratio_of_gaussian_or_bv
        X hX q hq W hW a hapos hbranch
    by_cases hxa : x ≤ a
    · have hWx : 0 ≤ W x := hW.2.1 x hx
      have hWa : 0 < W a :=
        scaleFunction_strict_pos_of_standing X hX q hq W hW a hapos
      have hd : 0 < deriv W a :=
        avram_wave3_02_scaleDeriv_pos_of_gaussian_or_bv
          X hX q hq W hW hbranch a hapos
      have hval : dividendValue X q x (barrierStrategy X x a) =
          ENNReal.ofReal (W x / deriv W a) := by
        calc
          _ = ENNReal.ofReal (W x / W a) * barrierSupValue X a q :=
            barrierStrategy_value_eq_exit_factor X hX q hq W hW a hapos x hx hxa
          _ = ENNReal.ofReal (W x / W a) *
                ENNReal.ofReal (W a / deriv W a) := by rw [hratio]
          _ = ENNReal.ofReal (W x / deriv W a) :=
            ennreal_scale_ratio_cancel (W x) (W a) (deriv W a) hWx hWa hd
      have hxnot : ¬ x < 0 := by linarith
      simpa [barrierValue, scaleDeriv, divE, hxnot, hxa, hzero] using hval
    · have hax : a < x := lt_of_not_ge hxa
      have hboundary : dividendValue X q a (barrierStrategy X a a) =
          ENNReal.ofReal (barrierValue W a a) := by
        rw [barrierValue_at_positive_barrier_eq_deriv_ratio W a hapos]
        calc
          _ = barrierSupValue X a q := barrierValue_self_eq_barrierSupValue X q a
          _ = ENNReal.ofReal (W a / deriv W a) := hratio
      have habove := barrierStrategy_above_value_of_boundary X q W a x ha0 hax
        hboundary (barrierValue_nonnegative_at_nonnegative_barrier
          X hX q hq W hW a ha0)
      exact habove
