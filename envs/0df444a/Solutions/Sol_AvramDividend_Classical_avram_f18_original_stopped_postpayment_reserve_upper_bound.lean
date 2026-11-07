-- Prove2me | solution 1 for AvramDividend.Classical.avram_f18_original_stopped_postpayment_reserve_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:06:44.222317+00:00
-- url     : https://prove2.me/submissions/71cb95fe-fed2-4ebe-99cb-6fd45f1107f0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_path_nonneg
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original stopped reserve cannot exceed the initial reserve plus its Lévy source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (K : ℝ) (hK : X.X t ω ≤ K) :
    (if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X t ω - rightLimit D t ω
      else riskProcess X x D t ω) ≤ x + K := by
  have hDnn : 0 ≤ D t ω :=
    dividendStrategy_path_nonneg D hD ω t
  have hRnn : 0 ≤ rightLimit D t ω :=
    le_trans hDnn (dividendStrategy_le_rightLimit D hD ω t)
  by_cases hs : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω
  · simp only [if_pos hs]
    linarith
  · simp only [if_neg hs, riskProcess]
    linarith
