-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger20_original_strict_prefix_postpayment_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:47:45.26613+00:00
-- url     : https://prove2.me/submissions/32672340-3a0f-4615-956c-5b5fd3ca7008

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

/-- The right limit of original prepayment reserve carries every strict
    positive-prefix lower bound, including to the postpayment zero cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ρ : ℝ≥0) (u : ℝ)
    (hprefix : ∀ t : ℝ≥0, 0 < t → t < ρ →
      u ≤ riskProcess X x D t ω) :
    ∀ t : ℝ≥0, t < ρ →
      u ≤ x + X.X t ω - rightLimit D t ω := by
  intro t ht
  have hT := riskProcess_tendsto_postPaymentReserve_right X x D hD ω t
  have hlt : ∀ᶠ s : ℝ≥0 in 𝓝[>] t, s < ρ :=
    (eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds
  have hgt : ∀ᶠ s : ℝ≥0 in 𝓝[>] t, t < s := self_mem_nhdsWithin
  have hLower : ∀ᶠ s : ℝ≥0 in 𝓝[>] t,
      u ≤ riskProcess X x D s ω := by
    filter_upwards [hgt, hlt] with s hts hsρ
    exact hprefix s (lt_of_le_of_lt (by exact zero_le) hts) hsρ
  have hNeg : ∀ᶠ s : ℝ≥0 in 𝓝[>] t,
      -(riskProcess X x D s ω) ≤ -u := by
    filter_upwards [hLower] with s hs
    linarith
  have hLimit := le_of_tendsto hT.neg hNeg
  linarith
