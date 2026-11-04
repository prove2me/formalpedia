-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_closed_cap_actual_right_discounted_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:37:08.785323+00:00
-- url     : https://prove2.me/submissions/cff5c4cc-15cd-4081-98fa-c7bfc5d935c8

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- The original closed-cap post-X, pre-right-payment reserve satisfies the discounted dividend budget, including boundary contact. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (q : ℝ) (ω : Ω) (t : ℝ≥0)
    (hactive : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    Real.exp (-q * (t : ℝ)) *
      ((rightLimit D t ω - D t ω) +
        w (x + X.X t ω - rightLimit D t ω) -
        w (riskProcess X x D t ω)) ≤ 0 := by
  have hmono : D t ω ≤ rightLimit D t ω :=
    dividendStrategy_le_rightLimit D hD.1.1 ω t
  have hpay := hD.1.2 ω t hactive
  have hpost : 0 ≤ x + X.X t ω - rightLimit D t ω := by
    have hpay' : rightLimit D t ω - D t ω ≤
        x + X.X t ω - D t ω := by
      simpa only [riskProcess] using hpay
    linarith only [hpay']
  have hprecap : ENNReal.ofReal (riskProcess X x D t ω) ≤ C := by
    by_cases ht : t = 0
    · subst t
      simpa [riskProcess, X.X_zero ω, hD.1.1.1 ω] using hxc
    · have htpos : (0 : ℝ≥0) < t :=
        lt_of_le_of_ne (show (0 : ℝ≥0) ≤ t from zero_le) (Ne.symm ht)
      exact hD.2 ω t htpos
  have hpostle : x + X.X t ω - rightLimit D t ω ≤
      riskProcess X x D t ω := by
    simp only [riskProcess]
    linarith
  have hpre : 0 ≤ riskProcess X x D t ω := le_trans hpost hpostle
  have hsec :=
    avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
      C hC w hw_cont hw_smooth hw_grad
      (riskProcess X x D t ω) hpre hprecap
      (x + X.X t ω - rightLimit D t ω)
      ⟨hpost, hpostle⟩
      (riskProcess X x D t ω)
      ⟨hpre, le_refl _⟩ hpostle
  have hcash : rightLimit D t ω - D t ω =
      riskProcess X x D t ω -
        (x + X.X t ω - rightLimit D t ω) := by
    simp only [riskProcess]
    ring
  have hnonpos :
      (rightLimit D t ω - D t ω) +
        w (x + X.X t ω - rightLimit D t ω) -
        w (riskProcess X x D t ω) ≤ 0 := by
    linarith only [hsec, hcash]
  exact mul_nonpos_of_nonneg_of_nonpos
    (le_of_lt (Real.exp_pos _)) hnonpos