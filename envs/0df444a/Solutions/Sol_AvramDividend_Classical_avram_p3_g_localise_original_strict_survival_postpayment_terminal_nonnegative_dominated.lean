-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_strict_survival_postpayment_terminal_nonnegative_dominated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:44:10.935236+00:00
-- url     : https://prove2.me/submissions/f5fd6be6-e33e-463b-b032-4c12d5ad6a86

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact canonical strict-ruin terminal is nonnegative and dominated
by the original prepayment discounted value, with cap contacts allowed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    ∀ (ω : Ω) (t : ℝ≥0),
      0 ≤ (if (t : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (t : ℝ))) *
          w (x + X.X t ω - rightLimit D t ω)
       else 0) ∧
      (if (t : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (t : ℝ))) *
          w (x + X.X t ω - rightLimit D t ω)
       else 0) ≤
      (if (t : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (t : ℝ))) *
          w (riskProcess X x D t ω)
       else 0) := by
  intro ω t
  by_cases hPre : (t : ℝ≥0∞) < ruinTime X x D ω
  · have hPost :=
      avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
        X w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
        x hx hxc D hD ω t
    have hDelta : 0 ≤ rightLimit D t ω - D t ω :=
      sub_nonneg.mpr (dividendStrategy_le_rightLimit D hD.1.1 ω t)
    have hJ := hjump ω t (Or.inr hPre)
    have hState :
        riskProcess X x D t ω -
          (rightLimit D t ω - D t ω) =
            x + X.X t ω - rightLimit D t ω := by
      simp only [riskProcess]
      ring
    rw [hState] at hJ
    have hBound :
        w (x + X.X t ω - rightLimit D t ω) ≤
          w (riskProcess X x D t ω) := by
      linarith
    have he : 0 ≤ Real.exp (-(q * (t : ℝ))) :=
      (Real.exp_pos _).le
    simp only [if_pos hPre]
    exact ⟨mul_nonneg he hPost,
      mul_le_mul_of_nonneg_left hBound he⟩
  · simp [hPre]
