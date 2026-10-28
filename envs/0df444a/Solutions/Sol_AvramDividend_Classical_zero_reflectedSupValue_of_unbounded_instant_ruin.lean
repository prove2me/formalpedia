-- Prove2me | solution 1 for AvramDividend.Classical.zero_reflectedSupValue_of_unbounded_instant_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:43:07.43983+00:00
-- url     : https://prove2.me/submissions/0a0ad387-a647-4bda-abee-d34d3e1a917e

import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_scale_zero
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_of_ae_instant_ruin
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Unbounded variation and a.s. instantaneous drawdown ruin close the zero-boundary equality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hRuin : ∀ᵐ ω ∂P, barrierRuinTime X 0 ω = 0) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by
  have hW0 : W 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW
  have hDet : barrierValue W 0 0 = 0 :=
    barrierValue_zero_of_scale_zero W hW0
  calc
    barrierSupValue X 0 q = 0 :=
      barrierSupValue_zero_of_ae_instant_ruin X 0 q hRuin
    _ = ENNReal.ofReal (barrierValue W 0 0) := by simp [hDet]
