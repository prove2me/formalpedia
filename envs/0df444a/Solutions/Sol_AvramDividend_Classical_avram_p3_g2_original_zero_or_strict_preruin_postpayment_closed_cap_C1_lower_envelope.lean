-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g2_original_zero_or_strict_preruin_postpayment_closed_cap_C1_lower_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T22:01:48.492697+00:00
-- url     : https://prove2.me/submissions/071b24f3-dc0e-4540-9932-289ef7fa3fe1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual right-postpayment reserve has the closed-cap unit-slope value
    lower bound, including immediate time-zero payment and cap contact. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      w 0 + (x + X.X t ω - rightLimit D t ω) ≤
        w (x + X.X t ω - rightLimit D t ω) := by
  intro ω t hpre
  have hsolv : 0 ≤ x + X.X t ω - rightLimit D t ω := by
    have hs := hD.1.2 ω t hpre
    dsimp [riskProcess] at hs
    linarith
  have hcap : ENNReal.ofReal (x + X.X t ω - rightLimit D t ω) ≤ C :=
    capped_postPaymentReserve_ofReal_le_cap X x C D hD hxc ω t
  exact avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
    C hC w hw_cont hw_smooth hw_grad
    (x + X.X t ω - rightLimit D t ω) hsolv hcap
    (x + X.X t ω - rightLimit D t ω) ⟨hsolv, le_rfl⟩
