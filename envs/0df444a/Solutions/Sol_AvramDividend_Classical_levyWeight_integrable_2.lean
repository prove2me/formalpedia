-- Prove2me | solution 2 for AvramDividend.Classical.levyWeight_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T11:41:33.214315+00:00
-- url     : https://prove2.me/submissions/07c91dc6-12d2-4572-a5c0-1e3044a6166d

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
  have hmeas : Measurable (fun y : ℝ => min 1 (y ^ 2)) := by
    fun_prop
  have hnonneg :
      0 ≤ᵐ[X.ν] (fun y : ℝ => min 1 (y ^ 2)) :=
    Filter.Eventually.of_forall (fun y =>
      le_min (by norm_num) (sq_nonneg y))
  exact
    (lintegral_ofReal_ne_top_iff_integrable
      hmeas.aestronglyMeasurable hnonneg).mp
      (ne_of_lt X.ν_integrable)
