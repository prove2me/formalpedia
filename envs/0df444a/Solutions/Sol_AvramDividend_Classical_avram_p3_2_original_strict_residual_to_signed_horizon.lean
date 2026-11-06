-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_strict_residual_to_signed_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:13:26.397802+00:00
-- url     : https://prove2.me/submissions/d5821162-9168-4430-828b-cebdfc2f1f7b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_canonical_signed_horizon_correction
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_cash_joint_L1_integral_add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- A genuine original strict residual controls the full signed right-horizon
cash and postpayment terminal, including the surviving horizon atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (E : Ω → ℝ) (hEInt : Integrable E P)
    (hEMean : (∫ ω, E ω ∂P) ≤ 0)
    (hStrict : ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ≤ w x + E ω) :
    let S : ℝ≥0 := ⟨T,hT⟩
    let Term : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, Term ω ∂P) ≤ w x := by
  let S : ℝ≥0 := ⟨T, hT⟩
  let Cash : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let Term : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω)
    else 0
  let Pre : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω)
    else 0)
  have hPair :=
    avram_wave8_04_original_BV_positive_horizon_signed_cash_joint_L1_integral_add
      X hBV q w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
      x D hD T hT hTpos
  obtain ⟨hPairInt, hPairEq⟩ := hPair
  have hSpos : 0 < S := by
    exact_mod_cast hTpos
  have hPoint : ∀ ω, Cash ω + Term ω ≤ Pre ω := by
    intro ω
    exact avram_p3_c_bvchain_original_canonical_signed_horizon_correction
      X x C D hD w hjump ω S hSpos q (le_of_lt hq)
  have hBound : ∀ᵐ ω ∂P, Cash ω + Term ω ≤ w x + E ω := by
    filter_upwards [hStrict] with ω hω
    exact (hPoint ω).trans hω
  have hUpperInt : Integrable (fun ω => w x + E ω) P :=
    (integrable_const (w x)).add hEInt
  have hBoundMean :
      (∫ ω, Cash ω + Term ω ∂P) ≤ w x + ∫ ω, E ω ∂P := by
    calc
      _ ≤ ∫ ω, w x + E ω ∂P :=
        integral_mono_ae hPairInt hUpperInt hBound
      _ = w x + ∫ ω, E ω ∂P := by
        rw [integral_add (integrable_const (w x)) hEInt]
        simp
  change (∫ ω, Cash ω ∂P) + (∫ ω, Term ω ∂P) ≤ w x
  calc
    _ = ∫ ω, Cash ω + Term ω ∂P := hPairEq.symm
    _ ≤ w x + ∫ ω, E ω ∂P := hBoundMean
    _ ≤ w x := by linarith only [hEMean]
