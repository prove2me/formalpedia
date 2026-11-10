-- Prove2me | solution 1 for AvramDividend.Classical.avram_gsource15_original_zerojump_ae_predictable_postpayment_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T17:50:52.126108+00:00
-- url     : https://prove2.me/submissions/2d0c20d5-56f1-46c8-ab47-791482407393

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_exact_leftLim_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
        (x + X.X t ω - rightLimit D t ω) +
          (rightLimit D t ω - D t ω) := by
  filter_upwards [avram_ubv_top11_original_zero_nu_global_continuous_ae X hν]
    with ω hcont
  intro t ht
  have hc : ContinuousAt (fun s : ℝ≥0 => X.X s ω) t :=
    hcont.continuousAt
  have hXt : Function.leftLim (fun s : ℝ≥0 => X.X s ω) t = X.X t ω :=
    hc.continuousWithinAt.leftLim_eq
  rw [avram_wave3_04_postPaymentReserve_exact_leftLim_identity
    X x D hD ω t ht, hXt]
  ring
