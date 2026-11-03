-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_04_original_BV_any_clock_strict_survival_terminal_max_eq_signed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:41:25.329658+00:00
-- url     : https://prove2.me/submissions/cdd7cc1f-2416-41cc-9be6-1052f90606a1

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
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
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) :
    ∀ ω,
      (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
       else 0) =
      (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)
       else 0) := by
  classical
  intro ω
  by_cases hsurv : (τ ω : ℝ≥0∞) < ruinTime X x D ω
  · have hpost :
        0 ≤ x + X.X (τ ω) ω - rightLimit D (τ ω) ω ∧
        ENNReal.ofReal (x + X.X (τ ω) ω -
          rightLimit D (τ ω) ω) ≤ C := by
      by_cases hzero : τ ω = 0
      · simpa only [hzero] using
          (capped_postPaymentReserve_initial_state X x C D hD hxc ω)
      · have htpos : (0 : ℝ≥0) < τ ω := by
          exact lt_of_le_of_ne zero_le (Ne.symm hzero)
        exact capped_postPaymentReserve_within_cap_before_ruin
          X x C D hD ω (τ ω) htpos hsurv
    have hsec :=
      avram_wave3_03_bv_full_cap_gradient_secant
        C hC w hw_cont hw_smooth hw_grad
        0 (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)
        (le_refl _) hpost.1 hpost.2
    have hwpost : 0 ≤ w (x + X.X (τ ω) ω -
        rightLimit D (τ ω) ω) := by
      linarith
    have hprod : 0 ≤ Real.exp (-(q * (τ ω : ℝ))) *
        w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω) :=
      mul_nonneg (le_of_lt (Real.exp_pos _)) hwpost
    simpa only [if_pos hsurv] using (max_eq_right hprod)
  · simp [hsurv]
