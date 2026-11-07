-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_positive_benchmark_signed_fatou_from_physical_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:55:37.287317+00:00
-- url     : https://prove2.me/submissions/ffb22119-7320-4aed-9bfc-86dbb0c9f580
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_strict_prefix_margin_sequence
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_source_vanishing_mean_physical_cells
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_centered_physical_error_signed_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_source_slack_exact_signed_fatou_normalisation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The positive-benchmark original BV certificate follows from the precise
stopped source-with-vanishing-L1-error physical-cell obligation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (hwpos : 0 < w x)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
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
  letI : IsProbabilityMeasure P := X.isProbability
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let S : ℝ≥0 := ⟨T, hT⟩
  let Payoff : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω)
    else 0)
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω)
    else 0)
  have hMesh := avram_p3_grid3_strict_prefix_margin_sequence T hTpos
  obtain ⟨hδpos, hδle, hδanti, hδlim⟩ :
      (∀ n, 0 < δ n) ∧ (∀ n, δ n ≤ T) ∧
        Antitone δ ∧ Tendsto δ atTop (𝓝 0) := by
    simpa only [δ] using hMesh
  have hFsource := avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
    X hBV x C D hD w hw_cont hw_neg q hq.le T hTpos hw_nonneg
    δ hδpos hδle hδanti hδlim
  have hFproperties : ∀ n, Measurable (F n) ∧
      Integrable (F n) P ∧ (∀ ω, 0 ≤ F n ω) := hFsource.1
  have hFatouPoint : ∀ ω, ENNReal.ofReal (Payoff ω) ≤
      liminf (fun n => ENNReal.ofReal (F n ω)) atTop := hFsource.2
  obtain ⟨M, B, Err, hSigned, hErrInt, hErrMean, hCells⟩ :=
    avram_p3_grid4_original_source_vanishing_mean_physical_cells
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump T hTpos
  let E : ℕ → Ω → ℝ := fun n ω => max (Err n ω) 0
  let e : ℕ → ℝ := fun n => ∫ ω, E n ω ∂P
  let Z : ℕ → Ω → ℝ := fun n ω => M n ω + B n ω + E n ω - e n
  have hCentered := avram_p3_grid4_centered_physical_error_signed_budget
    P (fun n ω => M n ω + B n ω) E hSigned hErrInt
  have hZ : ∀ n, Integrable (Z n) P ∧
      (∫ ω, Z n ω ∂P) ≤ 0 := by
    intro n
    simpa only [Z, e, E] using hCentered n
  have he : ∀ n, 0 ≤ e n := by
    intro n
    exact integral_nonneg (fun ω => le_max_right (Err n ω) 0)
  have he0 : Tendsto e atTop (𝓝 (0 : ℝ)) := by
    simpa only [e, E] using hErrMean
  have hApprox : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w x + (Z n ω + 0) + e n := by
    intro n
    filter_upwards [hCells n] with ω hω
    dsimp [F, Z, E, e] at *
    linarith
  obtain ⟨F', M', B', hF', hSigned', hPath', hFatou'⟩ :=
    avram_p3_grid4_source_slack_exact_signed_fatou_normalisation
      P (w x) hwpos Payoff F Z (fun _ _ => 0) e he he0
      (fun n => (hFproperties n).1)
      (fun n => (hFproperties n).2.1)
      (by intro n; exact Filter.Eventually.of_forall (hFproperties n).2.2)
      (by intro n; simpa only [add_zero] using hZ n)
      hApprox
      (Filter.Eventually.of_forall hFatouPoint)
  refine ⟨F', M', B',
    (fun n => (hF' n).1), (fun n => (hF' n).2.1),
    (fun n => (hF' n).2.2), hSigned', hPath', ?_⟩
  simpa only [Payoff, S] using hFatou'
