-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g2_original_all_nonnegative_horizon_expected_post_le_strict_or_initial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T19:09:16.520742+00:00
-- url     : https://prove2.me/submissions/c012f21e-94f1-42ec-ad4b-ae4c70a5b7fd

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_clock_full_cash_postpayment_source_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_strict_terminal_joint_L1_and_source_mean_le
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_full_cash_and_survival_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_signed_postbudget_le_prebudget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Expected, source-exact all-clock endpoint reconciliation.
The zero horizon uses the genuine initial right-atom budget with L1;
every positive horizon uses the separately proved full/strict expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (S : ℝ≥0) :
    let Closed : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let Open : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let Post : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0
    let Pre : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0
    (∫ ω, Closed ω + Post ω ∂P) ≤
      (if S = 0 then w x else (∫ ω, Open ω + Pre ω ∂P)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  dsimp only
  by_cases hs : S = 0
  · subst S
    have hcash :
        Integrable (fun ξ : Ω =>
          (∫⁻ t in paymentTimes (ruinTime X x D ξ) ∩ Iic (0 : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ξ)).toReal) P :=
      (avram_wave8_04_original_BV_full_cash_and_survival_terminal_L1
        X hBV q w hw_cont hw_neg x C D hD 0 (le_refl _)).1
    have hpost :
        Integrable (fun ξ : Ω =>
          if (0 : ℝ≥0∞) < ruinTime X x D ξ then
            w (x + X.X 0 ξ - rightLimit D 0 ξ) else 0) P := by
      have hh :=
        (avram_p3_g2_original_BV_strict_terminal_joint_L1_and_source_mean_le
          X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
          x hx hxc D hD q hjump (0 : ℝ≥0)).1
      simpa using hh
    have hbudget : ∀ ξ : Ω,
        (∫⁻ t in paymentTimes (ruinTime X x D ξ) ∩ Iic (0 : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ξ)).toReal +
          (if (0 : ℝ≥0∞) < ruinTime X x D ξ then
            w (x + X.X 0 ξ - rightLimit D 0 ξ) else 0) ≤ w x := by
      intro ξ
      exact avram_p3_g2_original_zero_clock_full_cash_postpayment_source_budget
        X hBV q w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
        x hx hxc D hD hjump ξ
    have hmean := integral_mono (hcash.add hpost)
      (integrable_const (w x)) hbudget
    simpa using hmean
  · have hpos : (0 : ℝ≥0) < S :=
      lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ S) (Ne.symm hs)
    have hTpos : 0 < (S : ℝ) := by exact_mod_cast hpos
    have hmean :=
      avram_p3_bv_original_signed_postbudget_le_prebudget
        X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
        x D hD hjump (S : ℝ) S.property hTpos
    have hS : (⟨(S : ℝ), S.property⟩ : ℝ≥0) = S := by
      apply Subtype.ext
      rfl
    simpa only [hS, if_neg hs] using hmean
