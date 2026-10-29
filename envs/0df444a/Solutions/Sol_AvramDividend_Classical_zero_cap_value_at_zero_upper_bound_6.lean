-- Prove2me | solution 6 for AvramDividend.Classical.zero_cap_value_at_zero_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:51:46.29993+00:00
-- url     : https://prove2.me/submissions/f2980a09-8d31-4c1f-bb72-d4e9daca3c8b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_boundary
import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    valueFunctionLe X q 0 0 ≤
      ENNReal.ofReal (barrierValue W 0 0) := by
  exact zero_cap_value_at_zero_upper_bound_of_boundary X hX q hq W
    (barrier_zero_boundary_value X hX q hq W hW)
