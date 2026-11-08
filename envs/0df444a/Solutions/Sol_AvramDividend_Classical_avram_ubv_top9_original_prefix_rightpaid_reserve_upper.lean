-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_original_prefix_rightpaid_reserve_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:25:30.271971+00:00
-- url     : https://prove2.me/submissions/4af43ad3-d3a1-4bb4-a276-01ad294b98ba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_path_nonneg
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A physical source ceiling survives nonnegative cumulative and right payments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (κ : Ω → ℝ≥0) (B : ℝ)
    (hXprefix : ∀ ω (t : ℝ≥0), t ≤ κ ω → X.X t ω ≤ B) :
    ∀ ω,
      (if κ ω = 0 ∨ (κ ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (κ ω) ω - rightLimit D (κ ω) ω
        else riskProcess X x D (κ ω) ω) ≤ x + B := by
  intro ω
  have hX : X.X (κ ω) ω ≤ B := hXprefix ω (κ ω) le_rfl
  have hDiv : ∀ t : ℝ≥0, 0 ≤ D t ω := by
    intro t
    exact dividendStrategy_path_nonneg D hD ω t
  have hRight : 0 ≤ rightLimit D (κ ω) ω := by
    unfold rightLimit
    apply le_ciInf
    intro s
    exact hDiv s
  by_cases hPre : κ ω = 0 ∨ (κ ω : ℝ≥0∞) < ruinTime X x D ω
  · simp only [if_pos hPre]
    linarith
  · simp only [if_neg hPre]
    have hNow : 0 ≤ D (κ ω) ω := hDiv (κ ω)
    unfold riskProcess
    linarith
