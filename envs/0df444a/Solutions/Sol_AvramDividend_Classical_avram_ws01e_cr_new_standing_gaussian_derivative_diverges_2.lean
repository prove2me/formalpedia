-- Prove2me | solution 2 for AvramDividend.Classical.avram_ws01e_cr_new_standing_gaussian_derivative_diverges
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:44:05.732995+00:00
-- url     : https://prove2.me/submissions/c871143c-fd4d-44c9-b97e-67d305f1589f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_cr_new_c1_derivative_growth_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_tendsto_atTop_of_eventually_ge_exp

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    Tendsto (deriv W) atTop atTop := by
  exact scaleDeriv_tendsto_atTop_of_eventually_ge_exp X hX q hq W hW
    (AvramDividend.Classical.avram_ws01e_cr_new_c1_derivative_growth_of_standing X hX q hq W hW
      (scaleFunction_contDiff_one_gaussian_without_standing X q hq W hW hσ))
