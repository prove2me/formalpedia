-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite12_original_positive_clock_postpayment_left_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T18:19:04.705004+00:00
-- url     : https://prove2.me/submissions/f76961e3-26c6-4387-a7e3-adb2f9d4990a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative

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
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      Tendsto (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
        (𝓝[<] t) (𝓝 (riskProcess X x D t ω)) := by
  filter_upwards [avram_ubv_top11_original_zero_nu_global_continuous_ae X hν]
    with ω hXcont
  intro t ht
  have hXt : Tendsto (fun s : ℝ≥0 => X.X s ω)
      (𝓝[<] t) (𝓝 (X.X t ω)) :=
    (hXcont.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hDt : Tendsto (fun s : ℝ≥0 => rightLimit D s ω)
      (𝓝[<] t) (𝓝 (D t ω)) :=
    avram_wave3_04_rightLimit_leftLimit_eq_dividend D hD ω t ht
  have hC : Tendsto (fun _ : ℝ≥0 => x) (𝓝[<] t) (𝓝 x) :=
    tendsto_const_nhds
  simpa only [riskProcess] using (hC.add hXt).sub hDt

