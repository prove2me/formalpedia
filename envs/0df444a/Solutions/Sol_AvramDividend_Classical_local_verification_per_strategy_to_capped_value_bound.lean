-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_per_strategy_to_capped_value_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:47:40.304006+00:00
-- url     : https://prove2.me/submissions/bd6817db-d98d-40c5-86cf-cd967d16408d

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (C : ℝ≥0∞) (x : ℝ) (w : ℝ → ℝ)
    (h : ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
      dividendValue X q x D ≤ ENNReal.ofReal (w x)) :
    valueFunctionLe X q C x ≤ ENNReal.ofReal (w x) := by
  unfold valueFunctionLe
  refine iSup_le fun D => iSup_le fun hD => ?_
  exact h D hD
