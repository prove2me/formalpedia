-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_single_signed_budget_to_fatou_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:53:08.33431+00:00
-- url     : https://prove2.me/submissions/0bb93f07-57d1-4abe-a5db-d49d96440f05

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_measurable_version
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (Z : Ω → ℝ)
    (hZint : Integrable Z P)
    (hZmean : (∫ ω, Z ω ∂P) ≤ 0)
    (hZpath : ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ≤ w x + Z ω) :
    ∃ F M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n)) ∧
      (∀ n, Integrable (F n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F n ω ≤ w x + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        ENNReal.ofReal (
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0)) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) := by
  obtain ⟨R, hRmeas, hRint, hRnonneg, hReq⟩ :=
    avram_p3_bv_original_strict_reward_measurable_version
      X hBV x C D hD w hw_cont hw_neg q
      (le_of_lt hq) T hT hTpos hw_nonneg
  refine ⟨(fun _ => R), (fun _ => Z), (fun _ => fun _ => 0),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hRmeas
  · intro n
    exact hRint
  · intro n
    exact hRnonneg
  · intro n
    simpa using And.intro hZint hZmean
  · intro n
    filter_upwards [hReq, hZpath] with ω hEq hBudget
    simpa [hEq] using hBudget
  · filter_upwards [hReq] with ω hEq
    simp [hEq]
