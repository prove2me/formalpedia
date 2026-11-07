-- Prove2me | solution 1 for AvramDividend.Classical.avram_route9_original_stopped_grid_family_HJB_expected_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:36:00.798003+00:00
-- url     : https://prove2.me/submissions/52a3918c-363b-4f75-a204-cb650123c1c8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_route6_original_stopped_predictable_prefix_full_hjb_sign
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original stopped BV HJB sign integrates on each grid in a family. -/
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
        ENNReal.ofReal (riskProcess X x D (u n i) ω) < C) :
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
        Integrable G P → (∫ ω, G ω ∂P) ≤ 0) := by
  have hEach : ∀ n, ∃ j : Ω → ℕ,
      (∀ ω, j ω ≤ m n) ∧
      (∀ ω i, i < m n →
        ((u n i : WithTop ℝ≥0) < τ n ω ↔ i < j ω)) ∧
      (∀ i, MeasurableSet[𝓕.rightCont (u n i)] {ω : Ω | i < j ω}) ∧
      (∀ s : Set ℕ, MeasurableSet (j ⁻¹' s)) ∧
      (∀ ω,
        (∑ i ∈ Finset.range (j ω),
          Real.exp (-(q * (u n i : ℝ))) *
            (((u n (i + 1) : ℝ) - (u n i : ℝ)) *
              (X.generator w (riskProcess X x D (u n i) ω) -
                q * w (riskProcess X x D (u n i) ω)) +
            (D (u n (i + 1)) ω - D (u n i) ω) *
              (1 - deriv w (riskProcess X x D (u n i) ω)))) ≤ 0) := by
    intro n
    exact avram_route6_original_stopped_predictable_prefix_full_hjb_sign
      X hBV q w C hw_gen hw_grad x D hD (τ n) (hStop n)
      (u n) (hu n) (m n) (hInterior n)
  choose k hk using hEach
  refine ⟨k, ?_, ?_, ?_, ?_, ?_⟩
  · intro n ω
    exact (hk n).1 ω
  · intro n ω i hi
    exact (hk n).2.1 ω i hi
  · intro n i
    exact (hk n).2.2.1 i
  · intro n s
    exact (hk n).2.2.2.1 s
  · intro n
    dsimp
    intro hInt
    apply integral_nonpos_of_ae
    exact Filter.Eventually.of_forall (hk n).2.2.2.2
