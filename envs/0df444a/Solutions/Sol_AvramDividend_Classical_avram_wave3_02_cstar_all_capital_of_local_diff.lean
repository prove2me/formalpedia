-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_cstar_all_capital_of_local_diff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T08:05:25.035526+00:00
-- url     : https://prove2.me/submissions/0a8a0c60-b9d0-4b66-bb83-58a14b0142df

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_deriv_pos_of_pointwise_diff
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_capital_of_local_deriv_nonzero
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_zero_all_capital
import Mathlib.Analysis.Calculus.FDeriv.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Genuine all-capital dividend value at finite cstar requires only local
differentiability at the positive barrier, with a separate zero-barrier case. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (hlocal : 0 < (cstar W).toReal →
      DifferentiableAt ℝ W (cstar W).toReal) :
    ∀ x : ℝ, 0 ≤ x →
      dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
        ENNReal.ofReal (vcstar W x) := by
  intro x hx
  let a : ℝ := (cstar W).toReal
  change dividendValue X q x (barrierStrategy X x a) =
    ENNReal.ofReal (barrierValue W a x)
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  by_cases hz : a = 0
  · simpa [hz] using
      (barrier_strategy_value_zero_all_capital X hX q hq W hW x hx)
  · have ha : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hz)
    have hd : 0 < deriv W a :=
      avram_wave3_02_deriv_pos_of_pointwise_diff X hX q hq W hW a ha (hlocal ha)
    exact avram_wave3_02_all_capital_of_local_deriv_nonzero
      X hX q hq W hW a ha (ne_of_gt hd) x hx
