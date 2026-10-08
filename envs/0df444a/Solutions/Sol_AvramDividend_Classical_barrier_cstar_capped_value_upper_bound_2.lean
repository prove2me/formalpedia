-- Prove2me | solution 2 for AvramDividend.Classical.barrier_cstar_capped_value_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T18:13:25.332677+00:00
-- url     : https://prove2.me/submissions/3d5af0b5-eda6-46fd-9558-7369dda7c3e9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_capped_value_upper_bound_of_positive_cstar

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
  intro x hx
  by_cases hzero : cstar W = 0
  · have hz := zero_cap_value_upper_bound X hX q hq W hW x hx
    simpa only [hzero, vcstar, ENNReal.toReal_zero] using hz
  · have hcpos : 0 < cstar W := pos_iff_ne_zero.mpr hzero
    exact barrier_cstar_capped_value_upper_bound_of_positive_cstar
      X hX q hq W hW hc hcpos h_smooth x hx
