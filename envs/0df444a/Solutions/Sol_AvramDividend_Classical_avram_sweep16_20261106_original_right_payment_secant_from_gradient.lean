-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_20261106_original_right_payment_secant_from_gradient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:55:46.134495+00:00
-- url     : https://prove2.me/submissions/c453ba9e-a3d1-4e61-9ce4-21876f57e403

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightJump_decomposition
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_within_cap_before_ruin
import Theorems.Thm_AvramDividend_Classical_admissibleLe_riskProcess_le_cap_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ (ω : Ω) (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) := by
  have hC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.of_le (by norm_num)
  intro ω t ht
  have hparts :=
    postPaymentReserve_rightJump_decomposition X x D hD.1.1 ω t
  have hpost :
      0 ≤ x + X.X t ω - rightLimit D t ω ∧
      ENNReal.ofReal (x + X.X t ω - rightLimit D t ω) ≤ C := by
    rcases ht with hzero | hbefore
    · subst t
      exact capped_postPaymentReserve_initial_state X x C D hD hxc ω
    · by_cases ht0 : t = 0
      · subst t
        exact capped_postPaymentReserve_initial_state X x C D hD hxc ω
      · exact capped_postPaymentReserve_within_cap_before_ruin
          X x C D hD ω t (pos_iff_ne_zero.mpr ht0) hbefore
  have hpostVal :
      riskProcess X x D t ω - (rightLimit D t ω - D t ω) =
        x + X.X t ω - rightLimit D t ω := by
    linarith [hparts.2.1]
  have hpostNonneg :
      0 ≤ riskProcess X x D t ω -
        (rightLimit D t ω - D t ω) := by
    rw [hpostVal]
    exact hpost.1
  have hriskCap :=
    admissibleLe_riskProcess_le_cap_all_times X x C D hD hxc ω t
  have hSecant := avram_wave3_03_bv_full_cap_gradient_secant
    C hC w hw_cont hC1 hw_grad
    (riskProcess X x D t ω - (rightLimit D t ω - D t ω))
    (riskProcess X x D t ω) hpostNonneg
    (by linarith [hparts.1]) hriskCap
  linarith
