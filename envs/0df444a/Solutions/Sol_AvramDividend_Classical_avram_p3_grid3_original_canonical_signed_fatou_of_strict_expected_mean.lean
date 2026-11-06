-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_canonical_signed_fatou_of_strict_expected_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:51:12.027194+00:00
-- url     : https://prove2.me/submissions/92cf2aa2-7f47-40da-8949-7e1f45b9ab3e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_measurable_version
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_source_witness_from_strict_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Conditional reconstruction of the exact signed Fatou witnesses from the true strict reward expected bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hMean :
      let S : ℝ≥0 := ⟨T, hT⟩
      let Strict : Ω → ℝ := fun ω =>
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)
      (∫ ω, Strict ω ∂P) ≤ w x) :
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
  let S : ℝ≥0 := ⟨T, hT⟩
  let Strict : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω)
    else 0)
  obtain ⟨R, hRm, hRi, hRpos, hReq⟩ :=
    avram_p3_bv_original_strict_reward_measurable_version
      X hBV x C D hD w hw_cont hw_neg q hq T hT hTpos hw_nonneg
  obtain ⟨E, hEi, hEmean, hEbound⟩ :=
    avram_p3_bv_original_source_witness_from_strict_mean
      X hBV x C D hD w hw_cont hw_neg q hq T hT hMean
  refine ⟨(fun _ : ℕ => R), (fun _ : ℕ => E),
    (fun _ : ℕ => fun _ : Ω => 0), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hRm
  · intro n
    exact hRi
  · intro n
    exact hRpos
  · intro n
    constructor
    · simpa only [add_zero] using hEi
    · simpa only [add_zero] using hEmean
  · intro n
    filter_upwards [hReq, hEbound] with ω hEq hBound
    change R ω ≤ w x + (E ω + 0)
    simpa only [add_zero, hEq] using hBound
  · filter_upwards [hReq] with ω hEq
    change ENNReal.ofReal (Strict ω) ≤
      liminf (fun _ : ℕ => ENNReal.ofReal (R ω)) atTop
    have hlim :
        liminf (fun _ : ℕ => ENNReal.ofReal (R ω)) atTop =
          ENNReal.ofReal (R ω) := by simp
    rw [hlim]
    exact le_of_eq (congrArg ENNReal.ofReal hEq.symm)
