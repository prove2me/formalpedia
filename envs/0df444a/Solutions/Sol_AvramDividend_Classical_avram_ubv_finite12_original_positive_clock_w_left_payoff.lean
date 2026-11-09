-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite12_original_positive_clock_w_left_payoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T18:24:02.175455+00:00
-- url     : https://prove2.me/submissions/0c567a01-b1f7-4915-bf96-316ca6e307f7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative

import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_original_positive_clock_postpayment_left_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      (t : ℝ≥0∞) ≤ ruinTime X x D ω →
      Tendsto (fun s : ℝ≥0 => w (x + X.X s ω - rightLimit D s ω))
        (𝓝[<] t) (𝓝 (w (riskProcess X x D t ω))) := by
  filter_upwards [
    avram_ubv_finite12_original_positive_clock_postpayment_left_tendsto
      X hν x D hD.1.1] with ω hWleft
  intro t ht htle
  have hE : ∀ᶠ s : ℝ≥0 in 𝓝[<] t,
      (s : ℝ≥0∞) < ruinTime X x D ω := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr hs) htle
  have hWnonneg : ∀ᶠ s : ℝ≥0 in 𝓝[<] t,
      0 ≤ x + X.X s ω - rightLimit D s ω := by
    filter_upwards [hE] with s hs
    exact avram_p4_e_localise_preruin_postpayment_nonnegative
      X x C D hD ω s (Or.inr hs)
  haveI : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hRt : 0 ≤ riskProcess X x D t ω :=
    isClosed_Ici.mem_of_tendsto (hWleft t ht) hWnonneg
  have hWwithin : Tendsto
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
      (𝓝[<] t) (𝓝[Ici (0 : ℝ)] (riskProcess X x D t ω)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hWleft t ht, hWnonneg⟩
  exact (hw.continuousWithinAt hRt).tendsto.comp hWwithin
