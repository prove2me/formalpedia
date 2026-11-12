-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys122_original_zero_source_postpayment_eq_risk_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:32:26.325204+00:00
-- url     : https://prove2.me/submissions/656bd97f-696f-4401-8852-759741a57860

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys118_original_dividend_rightLimit_ae_eq
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- On an original no-source-jump path, the postpayment drift
reserve agrees almost everywhere with the actual risk process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure ℝ≥0) [NullSingletonClass μ]
    (ω : Ω)
    (hpath : ∀ t : ℝ≥0, X.X t ω = (t : ℝ) * X.drift) :
    ∀ᵐ t ∂μ,
      x + ((t : ℝ≥0) : ℝ) * X.drift - rightLimit D t ω =
        riskProcess X x D t ω := by
  have hae :=
    avram_bvb_phys118_original_dividend_rightLimit_ae_eq
      X x C D hD μ ω
  filter_upwards [hae] with t ht
  rw [ht]
  simp only [riskProcess, hpath t]
