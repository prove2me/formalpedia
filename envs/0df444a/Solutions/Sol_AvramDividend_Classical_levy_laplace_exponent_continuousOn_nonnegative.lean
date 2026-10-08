-- Prove2me | solution 1 for AvramDividend.Classical.levy_laplace_exponent_continuousOn_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:25:41.919887+00:00
-- url     : https://prove2.me/submissions/f56d3208-5b8d-401e-ac50-f5217a8ee9ee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_continuousOn_Icc_nonneg
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ici_of_continuousOn_Icc_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ContinuousOn X.ψ (Ici (0 : ℝ)) := by
  exact continuousOn_Ici_of_continuousOn_Icc_zero X.ψ
    (fun B hB => levy_laplace_exponent_continuousOn_Icc_nonneg X B hB)
