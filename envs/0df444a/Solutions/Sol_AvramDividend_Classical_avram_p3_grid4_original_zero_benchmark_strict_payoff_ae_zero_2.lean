-- Prove2me | solution 2 for AvramDividend.Classical.avram_p3_grid4_original_zero_benchmark_strict_payoff_ae_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:31:20.332206+00:00
-- url     : https://prove2.me/submissions/3a42f5c5-504a-4a51-91ed-5ae7035e39d7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_strict_prefix_margin_sequence
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_source_vanishing_mean_physical_cells
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_horizon_payoff_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_signed_L1_mesh_error_fatou
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual zero-benchmark strict BV payoff vanishes once the original
same-grid compensated source bound and positive L1 error convergence hold. -/
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
  let Y : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  obtain ⟨hδpos, hδle, hδanti, hδzero⟩ :=
    avram_p3_grid3_strict_prefix_margin_sequence T hTpos
  have hFdata :=
    avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
      X hBV x C D hD w hw_cont hw_neg q hq.le T hTpos
      hw_nonneg δ hδpos hδle hδanti hδzero
  obtain ⟨M, B, Err, hSigned, hErrInt, hErrMean, hPath⟩ :=
    avram_p3_grid4_original_source_vanishing_mean_physical_cells
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hTpos
  have hYint : Integrable Y P :=
    avram_p3_bv_original_prebudget_L1
      X hBV x C D hD w hw_cont hw_neg q hq.le T hT
  have hYpos : 0 ≤ᵐ[P] Y :=
    Filter.Eventually.of_forall (fun ω =>
      avram_p3_grid4_original_strict_horizon_payoff_nonnegative
        X x D w q T hT hTpos hw_nonneg ω)
  have hFm (n : ℕ) : Measurable (F n) := (hFdata.1 n).1
  have hFi (n : ℕ) : Integrable (F n) P := (hFdata.1 n).2.1
  have hFn (n : ℕ) : 0 ≤ᵐ[P] F n :=
    Filter.Eventually.of_forall (hFdata.1 n).2.2
  have hMean : (∫ ω, Y ω ∂P) ≤ w x :=
    avram_p3_2_signed_L1_mesh_error_fatou P (w x) Y F
      (fun n ω => M n ω + B n ω) (fun n ω => max (Err n ω) 0)
      hYint hYpos hFm hFi hFn hSigned hErrInt hErrMean
      hPath (Filter.Eventually.of_forall hFdata.2)
  have hYmean0 : (∫ ω, Y ω ∂P) = 0 := by
    apply le_antisymm
    · simpa only [hwzero] using hMean
    · exact integral_nonneg_of_ae hYpos
  have hYzero : ∀ᵐ ω ∂P, Y ω = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hYpos hYint).mp hYmean0
  simpa only [Y, S] using hYzero
