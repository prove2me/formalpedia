-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_optimal_barrier_class_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T17:22:27.200069+00:00
-- url     : https://prove2.me/submissions/eec1b7b4-b594-4b7c-aa17-7913e222c98c

import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Operations
import Mathlib.Order.CompleteLattice.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_strategy_value_growth
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The best value among genuine nonnegative constant-barrier dividend
strategies is finite at every nonnegative starting reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 ≤ x) :
    (⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
      dividendValue X q x (barrierStrategy X x a)) < ⊤ := by
  obtain ⟨C, hC, hvalue⟩ :=
    avram_wave3_02_uniform_strategy_value_growth X hX q hq W hW
  have hbound :
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
        dividendValue X q x (barrierStrategy X x a)) ≤
      ENNReal.ofReal x + ENNReal.ofReal C := by
    refine iSup_le fun a => ?_
    refine iSup_le fun ha => ?_
    exact hvalue a x ha hx
  exact lt_of_le_of_lt hbound
    (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)
