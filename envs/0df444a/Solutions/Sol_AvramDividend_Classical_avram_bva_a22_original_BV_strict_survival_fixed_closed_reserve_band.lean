-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_BV_strict_survival_fixed_closed_reserve_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:23:13.192451+00:00
-- url     : https://prove2.me/submissions/5e3522b8-fd1d-4da2-a7c2-dc7f5760997a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_postpayment_deterministic_horizon_upper_strip
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hDs : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (hd : 0 ≤ X.drift) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      (x + X.X t ω - rightLimit D t ω) ∈
        Icc (0 : ℝ) (x + (T : ℝ) * X.drift) := by
  filter_upwards
    [avram_wave7_02_original_BV_postpayment_deterministic_horizon_upper_strip
      X hBV x D hDs T hd] with ω hupper
  intro t ht hpre
  exact ⟨
    avram_p4_e_localise_preruin_postpayment_nonnegative
      X x C D hD ω t hpre,
    hupper t ht⟩
