-- Prove2me | solution 3 for AvramDividend.Classical.avram_wave8_04_original_BV_positive_horizon_signed_stopped_HJB_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:42:40.746377+00:00
-- url     : https://prove2.me/submissions/a7018ff6-efc9-4acf-84d1-45b3cdb7c87c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_positive_horizon_stopped_prebudget_HJB
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_joint_horizon_terminal_accounting
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_cash_joint_L1_integral_add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact source-ruin horizon-atom accounting transfers the original BV
strict pre-rightpayment HJB supermartingale to the signed full budget. -/
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
  let Closed : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let Open : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let Signed : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω)
    else 0
  let Pre : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω)
    else 0
  have hFull := avram_wave8_04_original_BV_positive_horizon_signed_cash_joint_L1_integral_add
    X hBV q w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
    x D hD T hT hTpos
  change Integrable (fun ω => Closed ω + Signed ω) P ∧
    (∫ ω, Closed ω + Signed ω ∂P) =
      (∫ ω, Closed ω ∂P) + (∫ ω, Signed ω ∂P) at hFull
  have hPreInt := avram_p3_bv_original_prebudget_L1
    X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) T hT
  change Integrable (fun ω => Open ω + Pre ω) P at hPreInt
  have hPath := avram_p3_bv_joint_horizon_terminal_accounting
    X x C D hD q w hjump T hT hTpos
  change ∀ᵐ ω ∂P, Closed ω + Signed ω ≤ Open ω + Pre ω at hPath
  have hPreBudget := avram_p3_bv_original_positive_horizon_stopped_prebudget_HJB
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
    hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos
  change (∫ ω, Open ω + Pre ω ∂P) ≤ w x at hPreBudget
  have hOrder : (∫ ω, Closed ω + Signed ω ∂P) ≤
      (∫ ω, Open ω + Pre ω ∂P) :=
    integral_mono_ae hFull.1 hPreInt hPath
  change (∫ ω, Closed ω ∂P) + (∫ ω, Signed ω ∂P) ≤ w x
  rw [← hFull.2]
  exact hOrder.trans hPreBudget
