-- Prove2me | solution 12 for AvramDividend.Classical.avram_p3_bv_original_positive_horizon_stopped_prebudget_HJB
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T14:34:32.613976+00:00
-- url     : https://prove2.me/submissions/db1ac786-7422-4bb8-bc73-2b47aaa7098c
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

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An original-process HJB budget through the physical uniform grid,
without requiring integrability of the nonpositive generator drift. -/
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
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let v : ℕ → ℝ := fun n => T - δ n
  obtain ⟨u, hgrid, hmono, huniform⟩ :=
    avram_a19_physical_strict_horizon_uniform_grid T hTpos
  obtain ⟨M, B, hBform, hMint, hErrInt, hErrMean⟩ :=
    avram_a19_original_uniform_nonintegrable_tight_excess_certificate
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      T hTpos u hgrid hmono huniform
  have hBall : ∀ᵐ ω ∂P, ∀ n, B n ω ≤ 0 :=
    avram_redux9_original_uniform_grid_total_B_ae_nonpositive
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      T hTpos u hgrid hmono huniform B hBform
  have hBsign : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0 := by
    intro n
    filter_upwards [hBall] with ω hω
    exact hω n
  obtain ⟨hvmono, hv0, hvle, hvcofinal⟩ :=
    avram_p3_grid4_strict_physical_endpoint_cofinal_for_signed_fatou T hTpos
  let S : ℝ≥0 := ⟨T, hT⟩
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)
  let Err : ℕ → Ω → ℝ := fun n ω => F n ω - (w x + (M n ω + B n ω))
  have hPosInt : ∀ n, Integrable (fun ω => max (Err n ω) 0) P := by
    simpa only [Err, F] using hErrInt
  have hPosLim : Tendsto
      (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (nhds (0 : ℝ)) := by
    simpa only [Err, F] using hErrMean
  have hM : ∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) ≤ 0 := by
    intro n
    exact ⟨(hMint n).1, le_of_eq (hMint n).2⟩
  have hPhysical : ∀ n, ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (v n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0) ≤
      w x + (M n ω + B n ω) + max (Err n ω) 0 := by
    intro n
    refine Filter.Eventually.of_forall (fun ω => ?_)
    change F n ω ≤ w x + (M n ω + B n ω) + max (Err n ω) 0
    dsimp [Err]
    have hmax := le_max_left
      (F n ω - (w x + (M n ω + B n ω))) (0 : ℝ)
    linarith
  exact avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
    X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) S
    v hvmono hv0 hvle hvcofinal M B Err
    hM hBsign hPosInt hPosLim hPhysical
