-- Prove2me | solution 18 for AvramDividend.Classical.barrier_strategy_value
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T15:47:01.52565+00:00
-- url     : https://prove2.me/submissions/deefea9b-938f-464b-80cd-63dfc8d90fec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_scale_ratio
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

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
  have hExit := AvramDividend.Classical.barrierStrategy_value_eq_exit_factor
    X hX q hq W hW a ha x hx0 hxa
  have hSup := AvramDividend.Classical.barrierSupValue_eq_scale_ratio
    X hX q hq W hW a ha
  have hWaPos : 0 < W a :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hWnonneg : ∀ y : ℝ, 0 ≤ y → 0 ≤ W y := by
    have h := hW
    simp only [IsScaleFunction] at h
    exact h.2.1
  have hWxNonneg : 0 ≤ W x := hWnonneg x hx0
  have hDivNonneg : 0 ≤ W x / W a := div_nonneg hWxNonneg (le_of_lt hWaPos)
  have hWaNe : W a ≠ 0 := ne_of_gt hWaPos
  calc dividendValue X q x (barrierStrategy X x a)
      = ENNReal.ofReal (W x / W a) * ENNReal.ofReal (W a / deriv W a) := by
        rw [hExit, hSup]
    _ = ENNReal.ofReal ((W x / W a) * (W a / deriv W a)) := by
        rw [← ENNReal.ofReal_mul hDivNonneg]
    _ = ENNReal.ofReal (W x / deriv W a) := by
        congr 1
        by_cases hd : deriv W a = 0
        · simp [hd]
        · field_simp
