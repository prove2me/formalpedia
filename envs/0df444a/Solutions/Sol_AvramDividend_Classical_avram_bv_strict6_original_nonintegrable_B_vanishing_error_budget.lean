-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:46:20.756562+00:00
-- url     : https://prove2.me/submissions/a0a59378-0067-40b3-98c2-b5e23a573b41

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep14_original_BV_vanishing_error_strict_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hu : ∀ n, 0 ≤ u n) (hbelow : ∀ n, u n ≤ (S : ℝ))
    (hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n)
    (M B Err : ℕ → Ω → ℝ) :
    let Cash : ℝ → Ω → ℝ := fun r ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio r,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal
    let Term : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0
    ∀ (hM : ∀ n, Integrable (M n) P ∧
        (∫ ω, M n ω ∂P) ≤ 0)
      (hB : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
      (hErrInt : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
      (hErrMean : Tendsto
        (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (nhds 0))
      (hPhysical : ∀ n, ∀ᵐ ω ∂P,
        Cash (u n) ω + Term ω ≤
          w x + (M n ω + B n ω) + max (Err n ω) 0),
    (∫ ω, Cash (S : ℝ) ω + Term ω ∂P) ≤ w x := by
  intro Cash Term hM hB hErrInt hErrMean hPhysical
  have hSigned0 : ∀ n, Integrable (fun ω => M n ω + (0 : ℝ)) P ∧
      (∫ ω, M n ω + (0 : ℝ) ∂P) ≤ 0 := by
    intro n
    simpa only [add_zero] using hM n
  have hPhysical0 : ∀ n, ∀ᵐ ω ∂P,
      Cash (u n) ω + Term ω ≤
        w x + (M n ω + (0 : ℝ)) + max (Err n ω) 0 := by
    intro n
    filter_upwards [hB n, hPhysical n] with ω hb hp
    linarith
  exact avram_integration_sweep14_original_BV_vanishing_error_strict_mean
    X hBV x C D hD w hw_cont hw_neg q hq S
    u hmono hu hbelow hcover M (fun _ _ => 0) Err
    hSigned0 hErrInt hErrMean hPhysical0
