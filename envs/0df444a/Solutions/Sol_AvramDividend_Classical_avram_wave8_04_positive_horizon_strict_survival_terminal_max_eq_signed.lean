-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_04_positive_horizon_strict_survival_terminal_max_eq_signed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:22:00.300199+00:00
-- url     : https://prove2.me/submissions/7820f437-ea8a-4186-b1d9-60f8fa155085

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_within_cap_before_ruin
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T,hT⟩
    ∀ ω,
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω))
       else 0) =
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
       else 0) := by
  classical
  dsimp
  intro ω
  let S : ℝ≥0 := ⟨T,hT⟩
  change
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * T)) *
        w (x + X.X S ω - rightLimit D S ω))
     else 0) =
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) *
        w (x + X.X S ω - rightLimit D S ω)
     else 0)
  by_cases hsurv : (S : ℝ≥0∞) < ruinTime X x D ω
  · have htpos : (0 : ℝ≥0) < S := by
      exact_mod_cast hTpos
    obtain ⟨hpost0, hpostC⟩ :=
      capped_postPaymentReserve_within_cap_before_ruin
        X x C D hD ω S htpos hsurv
    have hsec :=
      avram_wave3_03_bv_full_cap_gradient_secant
        C hC w hw_cont hw_smooth hw_grad
        0 (x + X.X S ω - rightLimit D S ω)
        (le_refl _) hpost0 hpostC
    have hwpost : 0 ≤ w (x + X.X S ω - rightLimit D S ω) := by
      linarith
    have hprod : 0 ≤ Real.exp (-(q * T)) *
        w (x + X.X S ω - rightLimit D S ω) :=
      mul_nonneg (le_of_lt (Real.exp_pos _)) hwpost
    simpa only [if_pos hsurv] using (max_eq_right hprod)
  · simp [hsurv]
