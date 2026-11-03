-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_17_original_BV_complement_cash_deficit_criterion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:03:55.954215+00:00
-- url     : https://prove2.me/submissions/427384d5-dd73-46fa-9e2a-8555c972ddcf

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_bounded_random_clock_cash_integrable
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
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * X.drift ≤ w x)) :
    let Cash : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let DriftSlack : ℝ := x + T * X.drift - w x
    let BudgetDeficit : ℝ := x + T * X.drift - ∫ ω, Cash ω ∂P
    0 < T ∧ 0 < X.drift ∧ Integrable Cash P ∧
    0 < DriftSlack ∧ 0 ≤ BudgetDeficit ∧
    ((∫ ω, Cash ω ∂P) ≤ w x ↔ DriftSlack ≤ BudgetDeficit) := by
  dsimp only
  obtain ⟨hTpos, hdpos, hgap, hcash⟩ :=
    avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
      X hX hBV q hq w C hC hw_cont hw0 hw_smooth hw_grad
      x hx hxc D hD T hT hEnvelope
  have hInt : Integrable
      (fun ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P := by
    let tN : ℝ≥0 := ⟨T, hT⟩
    let τ : Ω → ℝ≥0 := fun _ => tN
    have hbound : ∀ ω, τ ω ≤ tN := by intro ω; exact le_rfl
    have hmeas : Measurable (fun ω : Ω => ((τ ω : ℝ≥0) : ℝ)) :=
      measurable_const
    have hb := avram_wave6_chat09_original_bv_bounded_random_clock_cash_integrable
      X hX hBV x hx C hxc D hD q (le_of_lt hq)
      tN τ hbound hmeas
    have hc : (tN : ℝ) = T := rfl
    simpa only [τ, hc] using hb
  refine ⟨hTpos, hdpos, hInt, hgap, ?_, ?_⟩
  · linarith
  · constructor <;> intro h <;> linarith
