-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict6_two_scale_original_strict_expected_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T08:36:07.15894+00:00
-- url     : https://prove2.me/submissions/7c024b7c-1b99-4c89-acae-e3b22b1b9b40

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep14_original_BV_vanishing_error_strict_mean
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_diagonal_nonnegative_error_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set AvramDividend.Classical
open scoped Topology NNReal ENNReal
noncomputable section

/-- Original BV strict HJB budget from two-scale physical-grid source estimates. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hu : ∀ n, 0 ≤ u n) (hbelow : ∀ n, u n ≤ (S : ℝ))
    (hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n)
    (M B Err : ℕ → ℕ → Ω → ℝ) :
    let Cash : ℝ → Ω → ℝ := fun r ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio r,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal
    let Term : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0
    ∀ (hSigned : ∀ k n, Integrable (fun ω => M k n ω + B k n ω) P ∧
        (∫ ω, M k n ω + B k n ω ∂P) ≤ 0)
      (hErrInt : ∀ k n, Integrable (fun ω => max (Err k n ω) 0) P)
      (hErrMean : ∀ k, Tendsto
        (fun n => ∫ ω, max (Err k n ω) 0 ∂P) atTop (𝓝 0))
      (hPhysical : ∀ k n, ∀ᵐ ω ∂P,
        Cash (u k) ω + Term ω ≤
          w x + (M k n ω + B k n ω) + max (Err k n ω) 0),
    (∫ ω, Cash (S : ℝ) ω + Term ω ∂P) ≤ w x := by
  intro Cash Term hSigned hErrInt hErrMean hPhysical
  let E : ℕ → ℕ → ℝ :=
    fun k n => ∫ ω, max (Err k n ω) 0 ∂P
  have hENonneg : ∀ k n, 0 ≤ E k n := by
    intro k n
    dsimp [E]
    apply integral_nonneg
    intro ω
    exact le_max_right _ _
  have hERow : ∀ k, Tendsto (fun n => E k n) atTop (𝓝 0) := by
    intro k
    exact hErrMean k
  obtain ⟨φ, _, hEDiag⟩ :=
    avram_bv_strict6_diagonal_nonnegative_error_mean E hENonneg hERow
  exact avram_integration_sweep14_original_BV_vanishing_error_strict_mean
    X hBV x C D hD w hw_cont hw_neg q hq S
    u hmono hu hbelow hcover
    (fun k ω => M k (φ k) ω)
    (fun k ω => B k (φ k) ω)
    (fun k ω => Err k (φ k) ω)
    (fun k => hSigned k (φ k))
    (fun k => hErrInt k (φ k))
    hEDiag
    (fun k => hPhysical k (φ k))
