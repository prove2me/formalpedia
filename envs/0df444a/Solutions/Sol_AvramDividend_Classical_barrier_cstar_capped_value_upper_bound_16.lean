-- Prove2me | solution 16 for AvramDividend.Classical.barrier_cstar_capped_value_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:20:11.061323+00:00
-- url     : https://prove2.me/submissions/6aaaeed8-7c84-477b-98f6-006c33cfc5dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_vcstar_zero_cstar_capped_upper
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_capped_value_upper_bound_of_positive_cstar
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The capped optimal barrier bound from its positive and zero barriers. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by
  classical
  by_cases hzero : cstar W = 0
  · exact avram_sweep16_original_vcstar_zero_cstar_capped_upper
      X hX q hq W hW hzero
  · have hpos : (0 : ℝ≥0∞) < cstar W := by
      exact lt_of_le_of_ne bot_le (Ne.symm hzero)
    exact barrier_cstar_capped_value_upper_bound_of_positive_cstar
      X hX q hq W hW hc hpos h_smooth
