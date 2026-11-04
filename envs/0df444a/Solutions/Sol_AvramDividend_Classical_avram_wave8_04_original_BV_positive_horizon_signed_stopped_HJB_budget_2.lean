-- Prove2me | solution 2 for AvramDividend.Classical.avram_wave8_04_original_BV_positive_horizon_signed_stopped_HJB_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:09:55.229394+00:00
-- url     : https://prove2.me/submissions/3af5a210-cfb4-4b29-a7a0-23b874e8a91e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_positive_horizon_stopped_prebudget_HJB
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_signed_postbudget_le_prebudget
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_cash_joint_L1_integral_add
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

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
    let S : ℝ≥0 := ⟨T, hT⟩
    let Term : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω)
      else 0
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, Term ω ∂P) ≤ w x := by
  let S : ℝ≥0 := ⟨T, hT⟩
  let CashOpen : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let CashClosed : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let Pre : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0
  let Post : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω) else 0
  have hPre : (∫ ω, CashOpen ω + Pre ω ∂P) ≤ w x := by
    exact avram_p3_bv_original_positive_horizon_stopped_prebudget_HJB
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T hT hTpos
  have hCompare :
      (∫ ω, CashClosed ω + Post ω ∂P) ≤
      (∫ ω, CashOpen ω + Pre ω ∂P) := by
    exact avram_p3_bv_original_signed_postbudget_le_prebudget
      X hBV q (le_of_lt hq) w C hC hw_cont hw0 hw_neg hw_smooth
      hw_grad x D hD hjump T hT hTpos
  have hAdd :
      (∫ ω, CashClosed ω + Post ω ∂P) =
      (∫ ω, CashClosed ω ∂P) + (∫ ω, Post ω ∂P) := by
    exact (avram_wave8_04_original_BV_positive_horizon_signed_cash_joint_L1_integral_add
      X hBV q w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
      x D hD T hT hTpos).2
  change (∫ ω, CashClosed ω ∂P) + (∫ ω, Post ω ∂P) ≤ w x
  calc
    (∫ ω, CashClosed ω ∂P) + (∫ ω, Post ω ∂P) =
        (∫ ω, CashClosed ω + Post ω ∂P) := hAdd.symm
    _ ≤ (∫ ω, CashOpen ω + Pre ω ∂P) := hCompare
    _ ≤ w x := hPre
