-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_ae_barrier_all_capital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T08:12:40.105992+00:00
-- url     : https://prove2.me/submissions/2c049c98-adba-4545-ab9c-cfafa0ee770c

import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_deriv_pos_of_pointwise_diff
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_capital_of_local_deriv_nonzero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Genuine Stieltjes reflected-barrier value agrees with scale valuation at
almost every positive barrier, without assuming global C1 regularity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ᵐ a : ℝ ∂(volume : Measure ℝ), 0 < a →
      ∀ x : ℝ, 0 ≤ x →
        dividendValue X q x (barrierStrategy X x a) =
          ENNReal.ofReal (barrierValue W a x) := by
  have hmono : Monotone W := scaleFunction_monotone X q W hW
  filter_upwards [hmono.ae_differentiableAt] with a hdiff ha
  have hd : 0 < deriv W a :=
    avram_wave3_02_deriv_pos_of_pointwise_diff X hX q hq W hW a ha hdiff
  exact avram_wave3_02_all_capital_of_local_deriv_nonzero
    X hX q hq W hW a ha (ne_of_gt hd)
