-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_positive_time_original_dividend_jump_w_drop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:30:58.312226+00:00
-- url     : https://prove2.me/submissions/732ac400-409a-468b-a4cd-a53953b9944b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Positive-time original payment: after any simultaneous source left jump,
the chronological right dividend atom reduces w by at least its cash amount.
The cap condition holds only at strictly positive times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (hPre : (t : ℝ≥0∞) < ruinTime X x D ω) :
    rightLimit D t ω - D t ω ≤
      w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)) := by
  have hAdmissible : IsAdmissible X x D := hD.1
  have hStrategy : IsDividendStrategy 𝓕 D := hAdmissible.1
  let U : ℝ := riskProcess X x D t ω
  let δ : ℝ := rightLimit D t ω - D t ω
  have hpay : 0 ≤ δ :=
    sub_nonneg.mpr (dividendStrategy_le_rightLimit D hStrategy ω t)
  have hsolv : δ ≤ U :=
    hAdmissible.2 ω t (Or.inr hPre)
  have hpost : 0 ≤ U - δ := by
    linarith only [hsolv]
  have hcap : ENNReal.ofReal U ≤ C := hD.2 ω t ht
  have horder : U - δ ≤ U := sub_le_self U hpay
  have hsec := avram_wave3_03_bv_full_cap_gradient_secant
    C hC w hw_cont hw_smooth hw_grad
    (U - δ) U hpost horder hcap
  change δ ≤ w U - w (U - δ)
  linarith only [hsec]
