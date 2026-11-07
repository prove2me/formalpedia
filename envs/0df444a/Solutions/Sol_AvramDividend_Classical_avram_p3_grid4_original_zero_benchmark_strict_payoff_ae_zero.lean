-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_zero_benchmark_strict_payoff_ae_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:09:12.93757+00:00
-- url     : https://prove2.me/submissions/8898175c-7b6d-432f-bb20-454b146b6aa8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_strict_prefix_margin_sequence
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_source_vanishing_mean_physical_cells
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_centered_physical_error_signed_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_vanishing_error_signed_residual_witness_direct
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_zero_benchmark_signed_source_forces_payoff_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original strict payoff vanishes when the full source-bound initial
benchmark is zero, after physical-error centring and Fatou. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (hwzero : w x = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
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
    ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) = 0 := by
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
  have he0 : Tendsto e atTop (𝓝 (0 : ℝ)) := by
    simpa only [e, E] using hErrMean
  have hApprox : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w x + Z n ω + e n := by
    intro n
    filter_upwards [hCells n] with ω hω
    dsimp [F, Z, E, e] at *
    linarith
  obtain ⟨R, hRint, hRmean, hRpay⟩ :=
    avram_p3_2_original_vanishing_error_signed_residual_witness_direct
      X hBV x C D hD w hw_cont hw_neg hw_nonneg q hq.le T hT hTpos
      F Z e
      (fun n => (hFproperties n).1)
      (fun n => (hFproperties n).2.1)
      (by intro n; exact Filter.Eventually.of_forall (hFproperties n).2.2)
      hZ he0 hApprox (Filter.Eventually.of_forall hFatouPoint)
  have hPayoffPos : ∀ ω, 0 ≤ Payoff ω := by
    intro ω
    have hCash : 0 ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal :=
      ENNReal.toReal_nonneg
    have hTerm : 0 ≤
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) := by
      split_ifs with hSurvive
      · exact mul_nonneg (Real.exp_nonneg _) (hw_nonneg ω S (by exact_mod_cast hTpos) hSurvive)
      · exact le_refl 0
    exact add_nonneg hCash hTerm
  have hPayoffZero : ∀ᵐ ω ∂P, Payoff ω = 0 :=
    avram_p3_grid4_zero_benchmark_signed_source_forces_payoff_zero
      P Payoff R
      (Filter.Eventually.of_forall hPayoffPos)
      hRint hRmean
      (by
        filter_upwards [hRpay] with ω hω
        simpa only [hwzero, zero_add, Payoff] using hω)
  simpa only [Payoff, S] using hPayoffZero
