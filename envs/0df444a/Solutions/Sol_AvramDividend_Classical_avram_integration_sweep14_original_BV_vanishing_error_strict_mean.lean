-- Prove2me | solution 1 for AvramDividend.Classical.avram_integration_sweep14_original_BV_vanishing_error_strict_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:44:14.604459+00:00
-- url     : https://prove2.me/submissions/4af1e05e-4e87-43bb-9e47-6ba25fc1aaab

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_expected_tendsto_real
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
    ∀ (hSigned : ∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0)
      (hErrInt : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
      (hErrMean : Tendsto
        (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (nhds 0))
      (hPhysical : ∀ n, ∀ᵐ ω ∂P,
        Cash (u n) ω + Term ω ≤
          w x + (M n ω + B n ω) + max (Err n ω) 0),
    (∫ ω, Cash (S : ℝ) ω + Term ω ∂P) ≤ w x := by
  intro Cash Term hSigned hErrInt hErrMean hPhysical
  letI : IsProbabilityMeasure P := X.isProbability
  have hS : (⟨(S : ℝ), NNReal.coe_nonneg S⟩ : ℝ≥0) = S := Subtype.ext rfl
  have hFull : Integrable (fun ω => Cash (S : ℝ) ω + Term ω) P := by
    simpa only [Cash, Term, hS] using
      (avram_p3_bv_original_prebudget_L1 X hBV x C D hD w hw_cont
        hw_neg q hq (S : ℝ) (NNReal.coe_nonneg S))
  have hCash (r : ℝ) (hr : 0 ≤ r) : Integrable (Cash r) P := by
    simpa only [Cash] using
      (avram_p3_bv_original_strict_cash_L1 X x C D hD q hq r hr)
  have hTerm : Integrable Term P := by
    have hSub : Integrable (fun ω => (Cash (S : ℝ) ω + Term ω) -
        Cash (S : ℝ) ω) P := hFull.sub (hCash _ (NNReal.coe_nonneg S))
    have hcancel (a b : ℝ) : a + b - a = b := by ring
    simpa only [hcancel] using hSub
  have hCashMean : Tendsto (fun n => ∫ ω, Cash (u n) ω ∂P) atTop
      (nhds (∫ ω, Cash (S : ℝ) ω ∂P)) := by
    simpa only [Cash] using
      (avram_p3_bv_original_strict_cash_cofinal_expected_tendsto_real
        X x C D hD q hq S u hmono hu hbelow hcover)
  have hMeanEq (r : ℝ) (hr : 0 ≤ r) :
      (∫ ω, Cash r ω + Term ω ∂P) =
        (∫ ω, Cash r ω ∂P) + (∫ ω, Term ω ∂P) :=
    integral_add (hCash r hr) hTerm
  have hMean :
      Tendsto (fun n => ∫ ω, Cash (u n) ω + Term ω ∂P) atTop
        (nhds (∫ ω, Cash (S : ℝ) ω + Term ω ∂P)) := by
    have hFn : (fun n => ∫ ω, Cash (u n) ω + Term ω ∂P) =
        (fun n => (∫ ω, Cash (u n) ω ∂P) +
          (∫ ω, Term ω ∂P)) := by
      funext n
      exact hMeanEq (u n) (hu n)
    rw [hFn, hMeanEq (S : ℝ) (NNReal.coe_nonneg S)]
    exact hCashMean.add tendsto_const_nhds
  have hGridBound (n : ℕ) :
      (∫ ω, Cash (u n) ω + Term ω ∂P) ≤
        w x + (∫ ω, max (Err n ω) 0 ∂P) := by
    have hSignedInt := (hSigned n).1
    have hRight : Integrable (fun ω =>
        w x + (M n ω + B n ω) + max (Err n ω) 0) P :=
      ((integrable_const (w x)).add hSignedInt).add (hErrInt n)
    have hBound := integral_mono_ae
      ((hCash (u n) (hu n)).add hTerm) hRight (hPhysical n)
    change (∫ ω, Cash (u n) ω + Term ω ∂P) ≤
      (∫ ω, w x + (M n ω + B n ω) + max (Err n ω) 0 ∂P) at hBound
    have hConst : (∫ _ : Ω, w x ∂P) = w x := by simp
    have hEqFirst :
        (∫ ω, w x + (M n ω + B n ω) + max (Err n ω) 0 ∂P) =
          (∫ ω, w x + (M n ω + B n ω) ∂P) +
          (∫ ω, max (Err n ω) 0 ∂P) :=
      integral_add ((integrable_const (w x)).add hSignedInt) (hErrInt n)
    have hEqSecond :
        (∫ ω, w x + (M n ω + B n ω) ∂P) =
          (∫ _ : Ω, w x ∂P) + (∫ ω, M n ω + B n ω ∂P) :=
      integral_add (integrable_const (w x)) hSignedInt
    have hEq : (∫ ω, w x + (M n ω + B n ω) +
        max (Err n ω) 0 ∂P) =
        w x + (∫ ω, M n ω + B n ω ∂P) +
          (∫ ω, max (Err n ω) 0 ∂P) := by
      calc
        _ = (∫ ω, w x + (M n ω + B n ω) ∂P) +
              (∫ ω, max (Err n ω) 0 ∂P) := hEqFirst
        _ = _ := by rw [hEqSecond, hConst]
    rw [hEq] at hBound
    linarith only [hBound, (hSigned n).2]
  have hLimit :
      Tendsto (fun n => (∫ ω, Cash (u n) ω + Term ω ∂P) -
        (w x + (∫ ω, max (Err n ω) 0 ∂P))) atTop
        (nhds ((∫ ω, Cash (S : ℝ) ω + Term ω ∂P) - w x)) := by
    simpa using hMean.sub (tendsto_const_nhds.add hErrMean)
  have hNonpos :
      (∫ ω, Cash (S : ℝ) ω + Term ω ∂P) - w x ≤ 0 := by
    apply le_of_tendsto hLimit
    exact Filter.Eventually.of_forall (fun n => sub_nonpos.mpr (hGridBound n))
  exact sub_nonpos.mp hNonpos
