-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_strict_single_signed_source_to_positive_fatou_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:26:42.140706+00:00
-- url     : https://prove2.me/submissions/2103f6c3-8dc8-40c4-9398-43b8b2d17d0d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_strict_prefix_margin_sequence
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_strict_discounted_cash_real_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original-process source budget supplies the remaining signed witness for the positive strict cash prefixes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hSource : ∃ Z : Ω → ℝ,
      Integrable Z P ∧ (∫ ω, Z ω ∂P) ≤ 0 ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0) ≤ w x + Z ω)) :
    ∃ F M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n)) ∧
      (∀ n, Integrable (F n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F n ω ≤ w x + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
        ENNReal.ofReal (
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0)) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) := by
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  obtain ⟨hδp, hδle, hδanti, hδlim⟩ :=
    avram_p3_grid3_strict_prefix_margin_sequence T hT
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω)
    else 0)
  have hF := avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
    X hBV x C D hD w hw_cont hw_neg q hq T hT hw_nonneg
    δ hδp hδle hδanti hδlim
  obtain ⟨Z, hZi, hZe, hZbound⟩ := hSource
  refine ⟨F, (fun _ => Z), (fun _ _ => 0), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (hF.1 n).1
  · intro n
    exact (hF.1 n).2.1
  · intro n
    exact Filter.Eventually.of_forall ((hF.1 n).2.2)
  · intro n
    constructor
    · simpa only [add_zero] using hZi
    · simpa only [add_zero] using hZe
  · intro n
    filter_upwards [hZbound] with ω hω
    have hn : 0 ≤ T - δ n := sub_nonneg.mpr (hδle n)
    have hnt : T - δ n ≤ T := by linarith [hδp n]
    have hCash := avram_p3_grid3_original_strict_discounted_cash_real_monotone
      X q hq x D hD.1.1 ω (T - δ n) T hn hnt
    change F n ω ≤ w x + (Z ω + 0)
    dsimp only [F]
    dsimp only at hω
    linarith only [hCash, hω]
  · exact Filter.Eventually.of_forall (fun ω => by
      simpa only [F, δ, S] using hF.2 ω)
