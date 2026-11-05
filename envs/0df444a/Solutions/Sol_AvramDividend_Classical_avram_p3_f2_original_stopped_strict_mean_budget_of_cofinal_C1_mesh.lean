-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_stopped_strict_mean_budget_of_cofinal_C1_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:48:16.53325+00:00
-- url     : https://prove2.me/submissions/4475e768-1fcb-4674-b65e-431dc2f6187f

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
/-- Original Stieltjes cash cofinality passes fixed killed-terminal expected budgets to the strict horizon. -/
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
    (K : ℝ)
    (hMesh : ∀ n,
      (∫ ω : Ω,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
        else 0) ∂P) ≤ K) :
    (∫ ω : Ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ K := by
  let Cash : ℝ → Ω → ℝ := fun r ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio r,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal
  let Term : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω) else 0
  have hS : (⟨(S : ℝ), NNReal.coe_nonneg S⟩ : ℝ≥0) = S := Subtype.ext rfl
  have hFull : Integrable (fun ω => Cash (S : ℝ) ω + Term ω) P := by
    simpa only [Cash, Term, hS] using
      (avram_p3_bv_original_prebudget_L1 X hBV x C D hD w hw_cont
        hw_neg q hq (S : ℝ) (by positivity))
  have hCash (r : ℝ) (hr : 0 ≤ r) : Integrable (Cash r) P := by
    simpa only [Cash] using
      (avram_p3_bv_original_strict_cash_L1 X x C D hD q hq r hr)
  have hTerm : Integrable Term P := by
    have hSub : Integrable (fun ω => (Cash (S : ℝ) ω + Term ω) -
        Cash (S : ℝ) ω) P := hFull.sub (hCash _ (by positivity))
    have hcancel (a b : ℝ) : a + b - a = b := by ring
    simpa only [hcancel] using hSub
  have hCashMean : Tendsto (fun n => ∫ ω, Cash (u n) ω ∂P) atTop
      (nhds (∫ ω, Cash (S : ℝ) ω ∂P)) := by
    simpa only [Cash] using
      (avram_p3_bv_original_strict_cash_cofinal_expected_tendsto_real
        X x C D hD q hq S u hmono hu hbelow hcover)
  have hMeanEq (r : ℝ) (hr : 0 ≤ r) :
      (∫ ω, Cash r ω + Term ω ∂P) =
        (∫ ω, Cash r ω ∂P) + (∫ ω, Term ω ∂P) := by
    exact integral_add (hCash r hr) hTerm
  have hMean :
      Tendsto (fun n => ∫ ω, Cash (u n) ω + Term ω ∂P) atTop
        (nhds (∫ ω, Cash (S : ℝ) ω + Term ω ∂P)) := by
    have hFn : (fun n => ∫ ω, Cash (u n) ω + Term ω ∂P) =
        (fun n => (∫ ω, Cash (u n) ω ∂P) +
          (∫ ω, Term ω ∂P)) := by
      funext n
      exact hMeanEq (u n) (hu n)
    rw [hFn, hMeanEq (S : ℝ) (by positivity)]
    exact hCashMean.add tendsto_const_nhds
  have hMesh' (n : ℕ) :
      (∫ ω, Cash (u n) ω + Term ω ∂P) ≤ K := by
    simpa only [Cash, Term] using hMesh n
  have hResult : (∫ ω, Cash (S : ℝ) ω + Term ω ∂P) ≤ K :=
    le_of_tendsto hMean (Filter.Eventually.of_forall hMesh')
  simpa only [Cash, Term] using hResult
