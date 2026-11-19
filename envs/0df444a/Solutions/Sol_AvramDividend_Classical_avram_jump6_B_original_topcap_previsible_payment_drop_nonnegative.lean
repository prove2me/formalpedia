-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_topcap_previsible_payment_drop_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:56:06.903633+00:00
-- url     : https://prove2.me/submissions/3567d256-3959-42ca-af59-9f570d412fc2

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
    (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (s t : ℝ≥0) (hst : s ≤ t)
    (hPre : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ w (x + X.X t ω - rightLimit D s ω) -
      w (x + X.X t ω - rightLimit D t ω) := by
  have hPost : 0 ≤ x + X.X t ω - rightLimit D t ω :=
    avram_p4_e_localise_preruin_postpayment_nonnegative
      X x C D hD ω t hPre
  have hRight : rightLimit D s ω ≤ rightLimit D t ω :=
    avram_wave3_03_dividendStrategy_rightLimit_monotone D hD.1.1 ω hst
  have hRes :
      x + X.X t ω - rightLimit D t ω ≤
      x + X.X t ω - rightLimit D s ω := by linarith only [hRight]
  have hVtop : C = ⊤ → ∀ y : ℝ, w y = w y := by
    intro _ y
    rfl
  have hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      w y = if y ≤ C.toReal then w y else w C.toReal + (y - C.toReal) := by
    intro h
    exact False.elim (h hTop)
  have hSec :=
    avram_wave5_04b_positive_ennreal_cap_extension_global_secant
      C hC w w hw_cont hw_smooth hw_grad hVtop hVfinite
      (x + X.X t ω - rightLimit D t ω)
      (x + X.X t ω - rightLimit D s ω) hPost hRes
  exact le_trans (sub_nonneg.mpr hRes) hSec
