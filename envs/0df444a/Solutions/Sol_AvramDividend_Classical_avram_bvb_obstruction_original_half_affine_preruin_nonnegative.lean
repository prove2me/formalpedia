-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_half_affine_preruin_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:44:49.309195+00:00
-- url     : https://prove2.me/submissions/de42dee2-fb42-4ebb-9376-e2a55a84d692

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonnegative_strictly_before_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) :
    ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ (if riskProcess X x D t ω < 0 then 0
         else 1 / 2 + riskProcess X x D t ω) := by
  intro ω t ht hRuin
  have hReserve :=
    riskProcess_nonnegative_strictly_before_ruin
      X x D ω t hRuin
  have hNot : ¬ riskProcess X x D t ω < 0 :=
    not_lt.mpr hReserve
  simp only [hNot, if_false]
  linarith
