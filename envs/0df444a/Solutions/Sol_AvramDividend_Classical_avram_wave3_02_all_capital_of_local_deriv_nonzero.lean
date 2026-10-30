-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_all_capital_of_local_deriv_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:05:54.24546+00:00
-- url     : https://prove2.me/submissions/999ae555-cafd-4449-a497-f281873ffa50

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_barrierSupValue_ratio_of_nonzero_deriv
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonneg
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
import Theorems.Thm_AvramDividend_Classical_ennreal_scale_ratio_cancel
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_above_value_of_boundary
import Theorems.Thm_AvramDividend_Classical_barrierValue_at_positive_barrier_eq_deriv_ratio
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_at_nonnegative_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Actual reflected value at any positive barrier with nonzero local scale slope. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (hNe : deriv W a ≠ 0) :
    ∀ x : ℝ, 0 ≤ x →
      dividendValue X q x (barrierStrategy X x a) =
        ENNReal.ofReal (barrierValue W a x) := by
  intro x hx
  have ha0 : 0 ≤ a := le_of_lt ha
  have hratio : barrierSupValue X a q =
      ENNReal.ofReal (W a / deriv W a) :=
    avram_wave3_02_barrierSupValue_ratio_of_nonzero_deriv
      X hX q hq W hW a ha hNe
  by_cases hxa : x ≤ a
  · have hWx : 0 ≤ W x := hW.2.1 x hx
    have hWa : 0 < W a :=
      scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
    have hnonneg : 0 ≤ deriv W a := scaleDeriv_nonneg X q W hW a ha
    have hd : 0 < deriv W a := lt_of_le_of_ne hnonneg (Ne.symm hNe)
    have hval : dividendValue X q x (barrierStrategy X x a) =
        ENNReal.ofReal (W x / deriv W a) := by
      calc
        _ = ENNReal.ofReal (W x / W a) * barrierSupValue X a q :=
          barrierStrategy_value_eq_exit_factor X hX q hq W hW a ha x hx hxa
        _ = ENNReal.ofReal (W x / W a) *
              ENNReal.ofReal (W a / deriv W a) := by rw [hratio]
        _ = ENNReal.ofReal (W x / deriv W a) :=
          ennreal_scale_ratio_cancel (W x) (W a) (deriv W a) hWx hWa hd
    have hxnot : ¬ x < 0 := by linarith
    simpa [barrierValue, scaleDeriv, divE, hxnot, hxa, ne_of_gt ha] using hval
  · have hax : a < x := lt_of_not_ge hxa
    have hboundary : dividendValue X q a (barrierStrategy X a a) =
        ENNReal.ofReal (barrierValue W a a) := by
      rw [barrierValue_at_positive_barrier_eq_deriv_ratio W a ha]
      calc
        _ = barrierSupValue X a q := barrierValue_self_eq_barrierSupValue X q a
        _ = ENNReal.ofReal (W a / deriv W a) := hratio
    exact barrierStrategy_above_value_of_boundary X q W a x ha0 hax
      hboundary (barrierValue_nonnegative_at_nonnegative_barrier
        X hX q hq W hW a ha0)
