-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_bv_expected_prebudget_to_triple_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:07:52.173311+00:00
-- url     : https://prove2.me/submissions/f514a4cf-fa88-49f4-af8b-01247a82efd5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_integrable_expected_budget_to_triple_mesh
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
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
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hBudget :
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
         else 0) ∂P) ≤ w x) :
    let Y : Ω → ℝ := fun ω =>
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
         else 0)
    ∃ Ymesh Mmesh Bmesh : ℕ → Ω → ℝ,
      ∃ M B DM DB : Ω → ℝ,
        (∀ n, AEStronglyMeasurable (Mmesh n) P) ∧
        (∀ n, AEStronglyMeasurable (Bmesh n) P) ∧
        Integrable DM P ∧ Integrable DB P ∧
        (∀ n, ∀ᵐ ω ∂P, |Mmesh n ω| ≤ DM ω) ∧
        (∀ n, ∀ᵐ ω ∂P, |Bmesh n ω| ≤ DB ω) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Ymesh n ω) atTop (nhds (Y ω))) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Mmesh n ω) atTop (nhds (M ω))) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Bmesh n ω) atTop (nhds (B ω))) ∧
        (∀ n, (∫ ω, Mmesh n ω ∂P) = 0) ∧
        (∀ n, (∫ ω, Bmesh n ω ∂P) ≤ 0) ∧
        (∀ᵐ ω ∂P, ∀ n, Ymesh n ω ≤ w x + Mmesh n ω + Bmesh n ω) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → ℝ := fun ω =>
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  have hYInt : Integrable Y P := by
    simpa only [Y] using
      (avram_p3_bv_original_prebudget_L1
        X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) T hT)
  have hYMean : (∫ ω, Y ω ∂P) ≤ w x := by
    simpa only [Y] using hBudget
  simpa only [Y] using
    (avram_sweep16_integrable_expected_budget_to_triple_mesh Y (w x) hYInt hYMean)
