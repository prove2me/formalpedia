-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger83_original_strict_prefix_right_endpoint_cash_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:21:11.107431+00:00
-- url     : https://prove2.me/submissions/88c8e011-65cb-4760-af32-de07f8ba1be7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_gledger30_original_topcap_right_endpoint_cash_without_C1
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ρ : ℝ≥0) (u : ℝ) (hu : 0 ≤ u)
    (hprefix : ∀ t : ℝ≥0, 0 < t → t < ρ →
      u ≤ riskProcess X x D t ω)
    (a b : ℝ≥0) (hab : a ≤ b) (hb : b < ρ)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_grad : ∀ y : ℝ, 0 < y → 1 ≤ deriv w y) :
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) *
        ENNReal.ofReal (w (x + X.X b ω - rightLimit D a ω) -
          w (x + X.X b ω - rightLimit D b ω)) +
      ENNReal.ofReal (q * ((b : ℝ) - (a : ℝ))) *
        dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) := by
  have hpost : 0 ≤ x + X.X b ω - rightLimit D b ω := by
    have hf := avram_gledger20_original_strict_prefix_postpayment_floor
      X x D hD ω ρ u hprefix b hb
    linarith
  have hinc : 0 ≤ rightLimit D b ω - rightLimit D a ω := by
    apply sub_nonneg.mpr
    exact (avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω) hab
  exact avram_gledger30_original_topcap_right_endpoint_cash_without_C1
    D hD ω a b hab q hq w hw_cont hw_grad
    (x + X.X b ω) hpost hinc
