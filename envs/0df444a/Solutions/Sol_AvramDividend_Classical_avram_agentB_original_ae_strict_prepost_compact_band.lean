-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_original_ae_strict_prepost_compact_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:11:01.201423+00:00
-- url     : https://prove2.me/submissions/60b1663c-80c3-41e5-9206-8e0cc331f0b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false
/-- A genuine strict original pre-dividend reserve compact band also
controls its same-path right-postpayment reserve at every positive clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (a b : ℝ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      a ≤ riskProcess X x D t ω ∧ riskProcess X x D t ω ≤ b) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      a ≤ x + X.X t ω - rightLimit D t ω ∧
        x + X.X t ω - rightLimit D t ω ≤ b := by
  filter_upwards [hprefix] with ω hω
  have hFloor : ∀ t : ℝ≥0, t < ρ ω →
      a ≤ x + X.X t ω - rightLimit D t ω :=
    avram_gledger20_original_strict_prefix_postpayment_floor
      X x D hD ω (ρ ω) a (fun t ht htρ => (hω t ht htρ).1)
  intro t ht htρ
  have hDle : D t ω ≤ rightLimit D t ω :=
    dividendStrategy_le_rightLimit D hD ω t
  have hBook := (hω t ht htρ).2
  refine ⟨hFloor t htρ, ?_⟩
  dsimp [riskProcess] at hBook
  linarith
