-- Prove2me | solution 1 for AvramDividend.Classical.avram_route6_original_stopped_predictable_prefix_full_hjb_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:45:23.48258+00:00
-- url     : https://prove2.me/submissions/a727f24e-b128-49b5-b59a-2a7a889d44a4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_original_stopped_measurable_predictable_prefix
import Theorems.Thm_AvramDividend_Classical_avram_route6_bv_original_physical_grid_full_signed_hjb_sum_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A measurable predictable stopped physical-grid prefix carries the HJB sign. -/
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
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ)
    (hInterior : ∀ ω i, i < m →
      (u i : WithTop ℝ≥0) < τ ω →
      0 < riskProcess X x D (u i) ω ∧
        ENNReal.ofReal (riskProcess X x D (u i) ω) < C) :
    ∃ k : Ω → ℕ,
      (∀ ω, k ω ≤ m) ∧
      (∀ ω i, i < m →
        ((u i : WithTop ℝ≥0) < τ ω ↔ i < k ω)) ∧
      (∀ i, MeasurableSet[𝓕.rightCont (u i)]
        {ω : Ω | i < k ω}) ∧
      (∀ s : Set ℕ, MeasurableSet (k ⁻¹' s)) ∧
      (∀ ω,
        (∑ i ∈ Finset.range (k ω),
          Real.exp (-(q * (u i : ℝ))) *
            (((u (i + 1) : ℝ) - (u i : ℝ)) *
              (X.generator w (riskProcess X x D (u i) ω) -
                q * w (riskProcess X x D (u i) ω)) +
            (D (u (i + 1)) ω - D (u i) ω) *
              (1 - deriv w (riskProcess X x D (u i) ω)))) ≤ 0) := by
  obtain ⟨k, hkBound, hMask, hPredict, hMeasurable⟩ :=
    avram_route_runner_original_stopped_measurable_predictable_prefix
      X τ hStop u hu m
  refine ⟨k, hkBound, hMask, hPredict, hMeasurable, ?_⟩
  intro ω
  have hregion : ∀ i ∈ Finset.range (k ω),
      0 < riskProcess X x D (u i) ω ∧
        ENNReal.ofReal (riskProcess X x D (u i) ω) < C := by
    intro i hi
    have hik : i < k ω := Finset.mem_range.mp hi
    have him : i < m := lt_of_lt_of_le hik (hkBound ω)
    exact hInterior ω i him ((hMask ω i him).2 hik)
  have hmon : Monotone (fun t : ℝ≥0 => D t ω) :=
    hD.1.1.2.1 ω
  have hdiv : ∀ i ∈ Finset.range (k ω),
      D (u i) ω ≤ D (u (i + 1)) ω := by
    intro i hi
    exact hmon (hu (Nat.le_succ i))
  exact avram_route6_bv_original_physical_grid_full_signed_hjb_sum_nonpos
    X hBV q w C hw_gen hw_grad x D ω u hu
    (Finset.range (k ω)) hregion hdiv
