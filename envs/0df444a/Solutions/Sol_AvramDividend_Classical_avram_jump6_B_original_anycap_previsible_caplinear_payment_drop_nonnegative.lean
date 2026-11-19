-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_anycap_previsible_caplinear_payment_drop_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:15:21.551622+00:00
-- url     : https://prove2.me/submissions/54f9a2c6-4b74-45a5-8ae2-aa6ef70fd943

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
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
    (C : ℝ≥0∞) (hC : 0 < C) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (s t : ℝ≥0) (hst : s ≤ t)
    (hPre : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ V (x + X.X t ω - rightLimit D s ω) -
      V (x + X.X t ω - rightLimit D t ω) := by
  have hPost : 0 ≤ x + X.X t ω - rightLimit D t ω :=
    avram_p4_e_localise_preruin_postpayment_nonnegative
      X x C D hD ω t hPre
  have hRight : rightLimit D s ω ≤ rightLimit D t ω :=
    avram_wave3_03_dividendStrategy_rightLimit_monotone D hD.1.1 ω hst
  have hRes :
      x + X.X t ω - rightLimit D t ω ≤
      x + X.X t ω - rightLimit D s ω := by linarith only [hRight]
  have hSec :=
    avram_wave5_04b_positive_ennreal_cap_extension_global_secant
      C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
      (x + X.X t ω - rightLimit D t ω)
      (x + X.X t ω - rightLimit D s ω) hPost hRes
  exact le_trans (sub_nonneg.mpr hRes) hSec
