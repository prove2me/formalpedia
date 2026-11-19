-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_anycap_initial_caplinear_postvalue_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:15:50.031304+00:00
-- url     : https://prove2.me/submissions/a5e29c83-683c-49b5-b5b7-be2cab0ce974

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
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
    (ω : Ω) :
    rightLimit D 0 ω + V (x - rightLimit D 0 ω) - V x ≤ 0 := by
  have hD0 : D 0 ω = 0 := hD.1.1.1 ω
  have hX0 : X.X 0 ω = 0 := X.X_zero ω
  have hPre : 0 ≤ x - rightLimit D 0 ω := by
    have h :=
      avram_p4_e_localise_preruin_postpayment_nonnegative
        X x C D hD ω 0 (Or.inl rfl)
    simpa [hX0] using h
  have hRight : 0 ≤ rightLimit D 0 ω := by
    have h := dividendStrategy_le_rightLimit D hD.1.1 ω 0
    simpa only [hD0] using h
  have hLower : x - rightLimit D 0 ω ≤ x := by
    linarith only [hRight]
  have hSec :=
    avram_wave5_04b_positive_ennreal_cap_extension_global_secant
      C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
      (x - rightLimit D 0 ω) x hPre hLower
  linarith only [hSec]
