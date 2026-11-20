-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_true_stop_terminal_caplinear_nonnegative_with_contact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:40:53.162172+00:00
-- url     : https://prove2.me/submissions/23fd7fd0-c7a4-4834-93a4-256977f0f9f8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_allcap_original_caplinear_value_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_preruin_actual_postpayment_solvency
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (ω : Ω) (t : ℝ≥0)
    (hCase : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω ∨
      riskProcess X x D t ω ≤ 0) :
    let Y : ℝ := if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X t ω - rightLimit D t ω
      else riskProcess X x D t ω
    0 ≤ Real.exp (-(q * (t : ℝ))) *
      (if ENNReal.ofReal Y ≤ C then w Y
       else w C.toReal + (Y - C.toReal)) := by
  dsimp only
  have he : 0 ≤ Real.exp (-(q * (t : ℝ))) := Real.exp_nonneg _
  have hdiff : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.of_le (by norm_num)
  by_cases hpre : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω
  · have hpoint : (t : ℝ) ∈ Icc (0 : ℝ) (t : ℝ) :=
      ⟨by exact_mod_cast t.property, le_rfl⟩
    have hsolv : 0 ≤ x + X.X t ω - rightLimit D t ω := by
      simpa using
        (avram_wave5_04b_closed_preruin_actual_postpayment_solvency
          X x C D hD ω t hpre (t : ℝ) hpoint)
    have hv := avram_f6_allcap_original_caplinear_value_nonnegative
      C hC w hw0 hw_cont hdiff hw_grad
      (x + X.X t ω - rightLimit D t ω) hsolv
    simpa only [if_pos hpre] using mul_nonneg he hv
  · have hruin : riskProcess X x D t ω ≤ 0 := by
      rcases hCase with h0 | hstrict | hneg
      · exact False.elim (hpre (Or.inl h0))
      · exact False.elim (hpre (Or.inr hstrict))
      · exact hneg
    have hzC : ENNReal.ofReal (riskProcess X x D t ω) ≤ C := by
      rw [ENNReal.ofReal_eq_zero.mpr hruin]
      exact bot_le
    have hval : 0 ≤ w (riskProcess X x D t ω) := by
      by_cases hz : riskProcess X x D t ω < 0
      · rw [hw_neg _ hz]
      · have hz0 : riskProcess X x D t ω = 0 :=
          le_antisymm hruin (le_of_not_gt hz)
        simpa [hz0] using hw0
    simpa only [if_neg hpre, if_pos hzC] using mul_nonneg he hval
