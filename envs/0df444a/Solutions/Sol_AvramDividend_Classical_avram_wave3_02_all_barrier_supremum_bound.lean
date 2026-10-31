-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_all_barrier_supremum_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T17:19:10.843523+00:00
-- url     : https://prove2.me/submissions/e9c13e64-d599-4f88-8e1a-29bd3443e72c

import Mathlib.Data.ENNReal.Real
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

/-- The best genuine reflected-barrier dividend value over all nonnegative
caps is finite and has one common affine upper bound in initial capital. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x →
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
        dividendValue X q x (barrierStrategy X x a)) ≤
      ENNReal.ofReal x + ENNReal.ofReal C := by
  obtain ⟨C, hC, hvalue⟩ :=
    avram_wave3_02_uniform_strategy_value_growth X hX q hq W hW
  refine ⟨C, hC, ?_⟩
  intro x hx
  refine iSup_le fun a => ?_
  refine iSup_le fun ha => ?_
  exact hvalue a x ha hx
