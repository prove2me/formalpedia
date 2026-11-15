-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB49_original_postpaid_upper_strip_indicator_le_true_prepaid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:13:55.407856+00:00
-- url     : https://prove2.me/submissions/998f434e-b89b-44cd-847d-2584355b3282

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    (if b < x + X.X t ω - rightLimit D t ω
      then (1 : ℝ) else 0) ≤
    (if b < riskProcess X x D t ω
      then (1 : ℝ) else 0) := by
  have hDmon : D t ω ≤ rightLimit D t ω :=
    dividendStrategy_le_rightLimit D hD ω t
  have hState :
      x + X.X t ω - rightLimit D t ω ≤ riskProcess X x D t ω := by
    dsimp [riskProcess]
    linarith
  by_cases hPost : b < x + X.X t ω - rightLimit D t ω
  · have hPre : b < riskProcess X x D t ω :=
      lt_of_lt_of_le hPost hState
    simp [hPost, hPre]
  · simp [hPost]
    split_ifs <;> norm_num
