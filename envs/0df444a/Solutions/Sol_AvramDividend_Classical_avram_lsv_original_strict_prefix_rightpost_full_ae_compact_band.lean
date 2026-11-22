-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_strict_prefix_rightpost_full_ae_compact_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:54:29.526639+00:00
-- url     : https://prove2.me/submissions/3284c104-e2dc-4b56-a25c-02fbbed08cb9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_gledger73_original_strict_prefix_postpayment_ceiling
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (a b : ℝ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      a ≤ riskProcess X x D t ω ∧ riskProcess X x D t ω ≤ b) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t < ρ ω →
      x + X.X t ω - rightLimit D t ω ∈ Icc a b := by
  filter_upwards [hprefix] with ω hw
  have hfloor : ∀ t : ℝ≥0, t < ρ ω →
      a ≤ x + X.X t ω - rightLimit D t ω :=
    avram_gledger20_original_strict_prefix_postpayment_floor
      X x D hD ω (ρ ω) a (fun t ht htρ => (hw t ht htρ).1)
  have hceil : ∀ t : ℝ≥0, t < ρ ω →
      x + X.X t ω - rightLimit D t ω ≤ b :=
    avram_gledger73_original_strict_prefix_postpayment_ceiling
      X x D hD ω (ρ ω) b (fun t ht htρ => (hw t ht htρ).2)
  intro t ht
  exact ⟨hfloor t ht, hceil t ht⟩
