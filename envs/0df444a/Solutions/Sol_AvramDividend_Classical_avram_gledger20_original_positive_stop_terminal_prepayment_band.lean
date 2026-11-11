-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger20_original_positive_stop_terminal_prepayment_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T11:10:55.796961+00:00
-- url     : https://prove2.me/submissions/0c275112-f8be-432e-bc6d-6e6fca9873c9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_original_positive_clock_postpayment_left_tendsto
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original zero-jump left-limit at a positive stopped clock preserves
    the bounded prepayment band, without paying a dividend at that clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (u b : ℝ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      u ≤ riskProcess X x D t ω ∧ riskProcess X x D t ω ≤ b) :
    ∀ᵐ ω ∂P, 0 < ρ ω →
      u ≤ riskProcess X x D (ρ ω) ω ∧
        riskProcess X x D (ρ ω) ω ≤ b := by
  filter_upwards
    [avram_ubv_finite12_original_positive_clock_postpayment_left_tendsto
      X hν x D hD, hprefix] with ω hleft hp
  intro hρ
  have hT := hleft (ρ ω) hρ
  have hbefore : ∀ᶠ s : ℝ≥0 in 𝓝[<] (ρ ω), s < ρ ω :=
    self_mem_nhdsWithin
  have hpositive : ∀ᶠ s : ℝ≥0 in 𝓝[<] (ρ ω), 0 < s :=
    (eventually_gt_nhds hρ).filter_mono nhdsWithin_le_nhds
  have hpost : ∀ s : ℝ≥0, s < ρ ω →
      u ≤ x + X.X s ω - rightLimit D s ω := by
    exact avram_gledger20_original_strict_prefix_postpayment_floor
      X x D hD ω (ρ ω) u (fun s hs hsρ => (hp s hs hsρ).1)
  have hLower : ∀ᶠ s : ℝ≥0 in 𝓝[<] (ρ ω),
      u ≤ x + X.X s ω - rightLimit D s ω := by
    filter_upwards [hbefore] with s hsρ
    exact hpost s hsρ
  have hUpper : ∀ᶠ s : ℝ≥0 in 𝓝[<] (ρ ω),
      x + X.X s ω - rightLimit D s ω ≤ b := by
    filter_upwards [hbefore, hpositive] with s hsρ hs0
    have hpre : riskProcess X x D s ω ≤ b := (hp s hs0 hsρ).2
    have hdiv := dividendStrategy_le_rightLimit D hD ω s
    change x + X.X s ω - D s ω ≤ b at hpre
    linarith
  have hNeg : ∀ᶠ s : ℝ≥0 in 𝓝[<] (ρ ω),
      -(x + X.X s ω - rightLimit D s ω) ≤ -u := by
    filter_upwards [hLower] with s hs
    linarith
  letI : (𝓝[<] (ρ ω)).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, hρ⟩
  have hlower := le_of_tendsto hT.neg hNeg
  have hupper := le_of_tendsto hT hUpper
  constructor <;> linarith
