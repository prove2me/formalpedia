-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_strict_residual_to_expected_prebudget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:21:37.858704+00:00
-- url     : https://prove2.me/submissions/c38ae499-a794-4706-b8f1-fdd5ca47eb89

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A physical strict original residual with nonpositive mean gives the
actual real Iio horizon expectation budget, without global martingale domination. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (E : Ω → ℝ) (hEInt : Integrable E P)
    (hEMean : (∫ ω, E ω ∂P) ≤ 0)
    (hStrict : ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ≤ w x + E ω) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by
  let S : ℝ≥0 := ⟨T, hT⟩
  let Y : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω)
    else 0)
  have hYInt : Integrable Y P :=
    avram_p3_bv_original_prebudget_L1 X hBV
      x C D hD w hw_cont hw_neg q hq T hT
  have hBound : ∀ᵐ ω ∂P, Y ω ≤ w x + E ω := by
    filter_upwards [hStrict] with ω hω
    exact hω
  have hUpperInt : Integrable (fun ω => w x + E ω) P :=
    (integrable_const (w x)).add hEInt
  have hMean : (∫ ω, Y ω ∂P) ≤ w x + ∫ ω, E ω ∂P := by
    calc
      _ ≤ ∫ ω, w x + E ω ∂P :=
        integral_mono_ae hYInt hUpperInt hBound
      _ = w x + ∫ ω, E ω ∂P := by
        rw [integral_add (integrable_const (w x)) hEInt]
        simp
  change (∫ ω, Y ω ∂P) ≤ w x
  linarith only [hMean, hEMean]
