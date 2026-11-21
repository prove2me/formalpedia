-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_strict_preruin_discounted_full_Stieltjes_cash_allgrid_any_event_uniform_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T17:37:13.321281+00:00
-- url     : https://prove2.me/submissions/fdd92ff0-4829-47f1-8eaa-e708b5bd2aef

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_all_strict_preruin_discounted_Stieltjes_cash_family_uniform_L2_budget
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (n : ℝ≥0) (ρ : ℕ → Ω → ℝ≥0)
    (hρle : ∀ k ω, ρ k ω ≤ n)
    (hρpre : ∀ k ω, (ρ k ω : ℝ≥0∞) <
      ruinTime X x D ω)
    (Cash : ℕ → Ω → ℝ)
    (hCash : ∀ k ω, Cash k ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Iic (ρ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hCashMeas : ∀ k, Measurable (Cash k))
    (A : Set Ω) (hA : MeasurableSet A) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ k, Integrable (fun ω => (Cash k ω)^2) P ∧
        (∫ ω in A, (Cash k ω)^2 ∂P) ≤ B := by
  obtain ⟨B, hB, hBase⟩ :=
    avram_pj_original_all_strict_preruin_discounted_Stieltjes_cash_family_uniform_L2_budget
      X hBV x D hD q hq n ρ hρle hρpre Cash hCash hCashMeas
  refine ⟨B, hB, ?_⟩
  intro k
  obtain ⟨hI, hUpper⟩ := hBase k
  refine ⟨hI, ?_⟩
  exact (integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall (fun ω => sq_nonneg (Cash k ω))) hI).trans hUpper
