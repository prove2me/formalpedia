-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger73_original_strict_prefix_postpayment_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:47:10.508209+00:00
-- url     : https://prove2.me/submissions/eb5cf9e4-f027-4574-832b-973766cc4d13

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_tendsto_postPaymentReserve_right
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A strict original prepayment ceiling persists at its right-hand
    postpayment limit, including the time-zero right payment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ρ : ℝ≥0) (b : ℝ)
    (hprefix : ∀ t : ℝ≥0, 0 < t → t < ρ →
      riskProcess X x D t ω ≤ b) :
    ∀ t : ℝ≥0, t < ρ →
      x + X.X t ω - rightLimit D t ω ≤ b := by
  intro t ht
  have hT := riskProcess_tendsto_postPaymentReserve_right X x D hD ω t
  have hlt : ∀ᶠ s : ℝ≥0 in 𝓝[>] t, s < ρ :=
    (eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds
  have hgt : ∀ᶠ s : ℝ≥0 in 𝓝[>] t, t < s := self_mem_nhdsWithin
  have hUpper : ∀ᶠ s : ℝ≥0 in 𝓝[>] t,
      riskProcess X x D s ω ≤ b := by
    filter_upwards [hgt, hlt] with s hts hsρ
    exact hprefix s (lt_of_le_of_lt (by exact zero_le) hts) hsρ
  exact le_of_tendsto hT hUpper
