-- Prove2me | solution 1 for AvramDividend.Classical.levyWeight_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T11:41:27.626966+00:00
-- url     : https://prove2.me/submissions/5cb0c8f7-de28-423b-b355-dd14c9d834e0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Integrable (fun y : ℝ => min 1 (y ^ 2)) X.ν := by
  have hmeas :
      AEStronglyMeasurable (fun y : ℝ => min 1 (y ^ 2)) X.ν := by
    fun_prop
  have hnonneg :
      0 ≤ᵐ[X.ν] (fun y : ℝ => min 1 (y ^ 2)) := by
    filter_upwards with y
    exact le_min zero_le_one (sq_nonneg y)
  exact
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).1
      (ne_of_lt X.ν_integrable)
