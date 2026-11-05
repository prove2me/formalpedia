-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_strict_budget_of_signed_cofinal_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:37:58.784887+00:00
-- url     : https://prove2.me/submissions/d4f16227-4292-46ba-bcc6-5c345b5717b9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_strict_terminal_joint_L1_and_source_mean_le
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_strict_mean_budget_of_cofinal_C1_mesh

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- Source-exact strict-horizon expectation bridge. A genuine original
signed correction for each cofinal mesh and a pathwise estimate suffice;
cash and pre-rightpayment survival terminal L1 are automatic from source. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (S : ℝ≥0) (u : ℕ → ℝ) (hmono : Monotone u)
    (hu : ∀ n, 0 ≤ u n) (hbelow : ∀ n, u n ≤ (S : ℝ))
    (hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n)
    (B : ℕ → Ω → ℝ)
    (hBint : ∀ n, Integrable (B n) P)
    (hBmean : ∀ n, (∫ ω, B n ω ∂P) ≤ 0)
    (hPath : ∀ n, ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
       else 0) ≤ w x + B n ω) :
    (∫ ω : Ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
       else 0) ∂P) ≤ w x := by
  apply avram_p3_f2_original_stopped_strict_mean_budget_of_cofinal_C1_mesh
    X hBV x C D hD w hw_cont hw_neg q hq S u hmono hu
    hbelow hcover (w x)
  intro n
  have hCash :=
    avram_p3_bv_original_strict_cash_L1
      X x C D hD q hq (u n) (hu n)
  have hTerminal :=
    avram_p3_g2_original_BV_strict_terminal_joint_L1_and_source_mean_le
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hx hxc D hD q hjump S
  dsimp only at hTerminal
  have hPre := hTerminal.2.1
  have hSum : Integrable (fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
       else 0)) P := hCash.add hPre
  have hR : Integrable (fun ω => w x + B n ω) P :=
    (integrable_const _).add (hBint n)
  calc
    (∫ ω : Ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
       else 0) ∂P) ≤ ∫ ω, w x + B n ω ∂P :=
        integral_mono_ae hSum hR (hPath n)
    _ = w x + (∫ ω, B n ω ∂P) := by
      simp [integral_add (integrable_const _) (hBint n)]
    _ ≤ w x := by linarith [hBmean n]
