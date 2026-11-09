-- Prove2me | solution 9 for AvramDividend.Classical.avram_integration_p3_original_strict_source_residual_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T23:01:41.777656+00:00
-- url     : https://prove2.me/submissions/4ab582b4-936d-4411-914a-2893ef536d24
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_physical_strict_horizon_uniform_grid
import Theorems.Thm_AvramDividend_Classical_avram_a19_original_uniform_nonintegrable_tight_excess_certificate
import Theorems.Thm_AvramDividend_Classical_avram_redux9_original_uniform_grid_total_B_ae_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_strict_physical_endpoint_cofinal_for_signed_fatou
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_source_witness_from_strict_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

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
    ∃ E : Ω → ℝ, Integrable E P ∧
      (∫ ω, E ω ∂P) ≤ 0 ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0) ≤ w x + E ω) := by
  classical
  haveI : IsProbabilityMeasure P := X.isProbability
  let S : ℝ≥0 := ⟨T, hT⟩
  obtain ⟨u, hgrid, hmono, huniform⟩ :=
    avram_a19_physical_strict_horizon_uniform_grid T hTpos
  obtain ⟨M, B, hBdef, hM, hErrInt, hErrMean⟩ :=
    avram_a19_original_uniform_nonintegrable_tight_excess_certificate
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump T hTpos u hgrid hmono huniform
  have hBsign : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0 := by
    have hAll : ∀ᵐ ω ∂P, ∀ n, B n ω ≤ 0 :=
      avram_redux9_original_uniform_grid_total_B_ae_nonpositive
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
        hw_grad x hx hxc D hD hw_nonneg hjump T hTpos
        u hgrid hmono huniform B hBdef
    intro n
    exact hAll.mono (fun ω hω => hω n)
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let v : ℕ → ℝ := fun n => T - δ n
  obtain ⟨hvm, hv0, hvT, hvcofinal⟩ :=
    avram_p3_grid4_strict_physical_endpoint_cofinal_for_signed_fatou T hTpos
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω)
    else 0)
  let Err : ℕ → Ω → ℝ := fun n ω =>
    F n ω - (w x + (M n ω + B n ω))
  have hMle : ∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) ≤ 0 := by
    intro n
    exact ⟨(hM n).1, le_of_eq (hM n).2⟩
  have hErrI : ∀ n, Integrable (fun ω => max (Err n ω) 0) P := by
    intro n
    exact hErrInt n
  have hErrT :
      Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (nhds (0 : ℝ)) :=
    hErrMean
  have hPhysical : ∀ n, ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (v n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ≤ w x + (M n ω + B n ω) + max (Err n ω) 0 := by
    intro n
    filter_upwards [] with ω
    change F n ω ≤ w x + (M n ω + B n ω) + max (Err n ω) 0
    dsimp only [Err]
    have h := le_max_left (F n ω - (w x + (M n ω + B n ω))) (0 : ℝ)
    linarith
  have hStrictMean :
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by
    exact avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
      X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq)
      S v hvm hv0 hvT hvcofinal M B Err
      hMle hBsign hErrI hErrT hPhysical
  exact avram_p3_bv_original_source_witness_from_strict_mean
    X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) T hT hStrictMean
