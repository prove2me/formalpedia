-- Prove2me | solution 3 for AvramDividend.Classical.barrier_cstar_capped_value_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T20:53:26.350619+00:00
-- url     : https://prove2.me/submissions/4fb4950a-3d4f-4576-be1a-07f10198dfd2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_capped_value_upper_bound_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by
  by_cases hc0 : cstar W = 0
  · intro x hx
    have hzero := zero_cap_value_upper_bound X hX q hq W hW x hx
    simpa [hc0, vcstar] using hzero
  · have hcpos : 0 < cstar W := bot_lt_iff_ne_bot.mpr hc0
    exact
      barrier_cstar_capped_value_upper_bound_of_positive_cstar
        X hX q hq W hW hc hcpos h_smooth
