-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g2_original_BV_strict_terminal_joint_L1_and_source_mean_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:36:50.076361+00:00
-- url     : https://prove2.me/submissions/89caa0a9-dcb4-4b21-a35d-2336a532384b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_preterminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_BV_strict_survival_postpayment_terminal_L1_from_source
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_BV_strict_survival_postpayment_expected_le_preterminal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source-exact terminal certificate at every deterministic ruin-truncated clock.
The original Levy fields supply the only zero-start and measure-finiteness facts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
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
            (rightLimit D t ω - D t ω)))
    (S : ℝ≥0) :
    let Post : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0
    let Pre : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) *
          w (riskProcess X x D S ω)
      else 0
    Integrable Post P ∧ Integrable Pre P ∧
      (∫ ω, Post ω ∂P) ≤ (∫ ω, Pre ω ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact
      avram_p3_g_localise_original_BV_strict_survival_postpayment_terminal_L1_from_source
        X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
        x hx hxc D hD q hjump S
  · exact
      avram_p3_bv_original_strict_preterminal_L1
        X hBV X.X_zero inferInstance x D hD.1.1
        w hw_cont hw_neg q S
  · exact
      avram_p3_g_localise_original_BV_strict_survival_postpayment_expected_le_preterminal
        X hBV X.X_zero inferInstance
        w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
        x hx hxc D hD q hjump S
