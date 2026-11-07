-- Prove2me | solution 1 for AvramDividend.Classical.avram_route9_original_stopped_grid_family_compensated_HJB_signed_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:51:42.771186+00:00
-- url     : https://prove2.me/submissions/e989f56b-c172-483f-830d-294d8f6f6ef7

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_route9_original_stopped_grid_family_HJB_expected_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Combine a genuine centred compensated source with each stopped HJB grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (τ : ℕ → Ω → WithTop ℝ≥0)
    (hStop : ∀ n, IsStoppingTime 𝓕.rightCont (τ n))
    (u : ℕ → ℕ → ℝ≥0) (hu : ∀ n, Monotone (u n))
    (m : ℕ → ℕ)
    (hInterior : ∀ n ω i, i < m n →
      (u n i : WithTop ℝ≥0) < τ n ω →
      0 < riskProcess X x D (u n i) ω ∧
        ENNReal.ofReal (riskProcess X x D (u n i) ω) < C)
    (M : ℕ → Ω → ℝ)
    (hMInt : ∀ n, Integrable (M n) P)
    (hMMean : ∀ n, (∫ ω, M n ω ∂P) = 0) :
    ∃ k : ℕ → Ω → ℕ,
      (∀ n ω, k n ω ≤ m n) ∧
      (∀ n ω i, i < m n →
        ((u n i : WithTop ℝ≥0) < τ n ω ↔ i < k n ω)) ∧
      (∀ n i, MeasurableSet[𝓕.rightCont (u n i)]
        {ω : Ω | i < k n ω}) ∧
      (∀ n (s : Set ℕ), MeasurableSet ((k n) ⁻¹' s)) ∧
      (∀ n,
        let G : Ω → ℝ := fun ω =>
          ∑ i ∈ Finset.range (k n ω),
            Real.exp (-(q * (u n i : ℝ))) *
              (((u n (i + 1) : ℝ) - (u n i : ℝ)) *
                (X.generator w (riskProcess X x D (u n i) ω) -
                  q * w (riskProcess X x D (u n i) ω)) +
              (D (u n (i + 1)) ω - D (u n i) ω) *
                (1 - deriv w (riskProcess X x D (u n i) ω)))
        Integrable G P →
          Integrable (fun ω => M n ω + G ω) P ∧
            (∫ ω, M n ω + G ω ∂P) ≤ 0) := by
  obtain ⟨k, hk, hMask, hPredict, hMeas, hBudget⟩ :=
    avram_route9_original_stopped_grid_family_HJB_expected_nonpos
      X hBV q w C hw_gen hw_grad x D hD
      τ hStop u hu m hInterior
  refine ⟨k, hk, hMask, hPredict, hMeas, ?_⟩
  intro n
  dsimp
  intro hGInt
  constructor
  · exact (hMInt n).add hGInt
  · rw [integral_add (hMInt n) hGInt, hMMean n]
    simpa only [zero_add] using hBudget n hGInt
