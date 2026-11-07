-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_positive_random_error_fatou_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:41:07.617921+00:00
-- url     : https://prove2.me/submissions/b671d5e8-c9a2-491f-aaa0-0245b8aca0e7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_random_positive_source_error_fatou_normalisation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Literal original stopped strict cash and surviving terminal admit the exact
signed Fatou witnesses once a genuine M/B physical comparison and vanishing
L¹ positive cell error are separately established. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hwpos : 0 < w x)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδle : ∀ n, δ n ≤ T) (hδanti : Antitone δ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (M B Err : ℕ → Ω → ℝ)
    (hSigned : ∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
      (∫ ω, M n ω + B n ω ∂P) ≤ 0)
    (hErrInt : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hErrMean : Tendsto
      (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (𝓝 0))
    (hPhysical : ∀ n, ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
       else 0) ≤
        w x + (M n ω + B n ω) + max (Err n ω) 0) :
    ∃ F' M' B' : ℕ → Ω → ℝ,
      (∀ n, Measurable (F' n)) ∧
      (∀ n, Integrable (F' n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F' n) ∧
      (∀ n, Integrable (fun ω => M' n ω + B' n ω) P ∧
        (∫ ω, M' n ω + B' n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F' n ω ≤ w x + (M' n ω + B' n ω)) ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        ENNReal.ofReal ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
       else 0)) ≤
          liminf (fun n => ENNReal.ofReal (F' n ω)) atTop) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let S : ℝ≥0 := ⟨T, hT⟩
  let F₀ : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
       else 0)
  let Y : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
       else 0)
  have hF :=
    avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
      X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq)
      T hTpos hw_nonneg δ hδpos hδle hδanti hδ
  have hFm : ∀ n, Measurable (F₀ n) := by
    intro n
    exact (hF.1 n).1
  have hFi : ∀ n, Integrable (F₀ n) P := by
    intro n
    exact (hF.1 n).2.1
  have hFp : ∀ n, 0 ≤ᵐ[P] F₀ n := by
    intro n
    filter_upwards [] with ω
    exact (hF.1 n).2.2 ω
  have hPhys : ∀ n, ∀ᵐ ω ∂P,
      F₀ n ω ≤ w x + (M n ω + B n ω) + max (Err n ω) 0 := by
    intro n
    exact hPhysical n
  have hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F₀ n ω)) atTop := by
    exact Filter.Eventually.of_forall hF.2
  obtain ⟨F', M', B', hF', hS', hP', hL'⟩ :=
    avram_p3_grid4_random_positive_source_error_fatou_normalisation
      (w x) hwpos Y F₀ M B Err
      hFm hFi hFp hSigned hErrInt hErrMean hPhys hFatou
  refine ⟨F', M', B', ?_, ?_, ?_, hS', hP', ?_⟩
  · intro n
    exact (hF' n).1
  · intro n
    exact (hF' n).2.1
  · intro n
    exact (hF' n).2.2
  · exact hL'
