-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g2_original_strict_preruin_prepayment_C1_nonnegative_from_closed_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T21:46:23.21008+00:00
-- url     : https://prove2.me/submissions/c4c130d0-4bd5-4041-b5c5-988ba71b75fe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_nonnegative_strictly_before_ruin
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightJump_decomposition
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Strict original pre-ruin HJB prepayment positivity includes cap contact. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0) ) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω) := by
  intro ω t ht hruin
  have hs : IsDividendStrategy 𝓕 D := hD.1.1
  have hUplus : 0 ≤ x + X.X t ω - rightLimit D t ω :=
    postPaymentReserve_nonnegative_strictly_before_ruin
      X x D hs ω t hruin
  have hdrop : x + X.X t ω - rightLimit D t ω ≤
      riskProcess X x D t ω :=
    (postPaymentReserve_rightJump_decomposition X x D hs ω t).2.2
  have hU : 0 ≤ riskProcess X x D t ω := hUplus.trans hdrop
  have hcap : ENNReal.ofReal (riskProcess X x D t ω) ≤ C :=
    hD.2 ω t ht
  have hmem :
      riskProcess X x D t ω ∈
        Icc (0 : ℝ) (riskProcess X x D t ω) :=
    ⟨hU, le_rfl⟩
  have hlower : w 0 + riskProcess X x D t ω ≤
      w (riskProcess X x D t ω) :=
    avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
      C hC w hw_cont hw_smooth hw_grad
      (riskProcess X x D t ω) hU hcap
      (riskProcess X x D t ω) hmem
  linarith
