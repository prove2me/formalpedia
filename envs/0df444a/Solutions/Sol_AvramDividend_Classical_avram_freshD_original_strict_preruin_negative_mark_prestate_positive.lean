-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_strict_preruin_negative_mark_prestate_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T09:06:19.156288+00:00
-- url     : https://prove2.me/submissions/25a7d423-c39b-48d7-b768-e0766076624c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω)
    (hz : X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t < 0) :
    0 < x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) t - D t ω := by
  have hr : 0 ≤ riskProcess X x D t ω :=
    riskProcess_nonneg_before_ruin X x D ω t ht
  dsimp [riskProcess] at hr
  linarith
