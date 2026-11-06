-- Prove2me | solution 5 for AvramDividend.Classical.avram_wave8_04_original_BV_positive_horizon_signed_stopped_HJB_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:33:22.670571+00:00
-- url     : https://prove2.me/submissions/d4976911-0226-49d0-9fc0-fb85562ef96b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_positive_horizon_stopped_prebudget_HJB
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_canonical_signed_horizon_correction
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_cash_joint_L1_integral_add
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Canonical positive-horizon signed BV budget from the strict prebudget
and proved original right-horizon cash/terminal correction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
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
  have hPreInt : Integrable Pre P := by
    exact avram_p3_bv_original_prebudget_L1 X hBV
      x C D hD w hw_cont hw_neg q (le_of_lt hq) T hT
  have hSpos : 0 < S := by
    exact_mod_cast hTpos
  have hPoint : ∀ ω, Cash ω + Term ω ≤ Pre ω := by
    intro ω
    exact avram_p3_c_bvchain_original_canonical_signed_horizon_correction
      X x C D hD w hjump ω S hSpos q (le_of_lt hq)
  have hExp : (∫ ω, Cash ω + Term ω ∂P) ≤
      (∫ ω, Pre ω ∂P) :=
    integral_mono hPairInt hPreInt hPoint
  have hPreBudget : (∫ ω, Pre ω ∂P) ≤ w x := by
    exact avram_p3_bv_original_positive_horizon_stopped_prebudget_HJB
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos
  change (∫ ω, Cash ω ∂P) + (∫ ω, Term ω ∂P) ≤ w x
  calc
    _ = ∫ ω, Cash ω + Term ω ∂P := hPairEq.symm
    _ ≤ ∫ ω, Pre ω ∂P := hExp
    _ ≤ w x := hPreBudget
