-- Prove2me | solution 1 for AvramDividend.Classical.avram_a53_raw_f0_conull_regularisation_preserves_adaptedness_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:12:11.361332+00:00
-- url     : https://prove2.me/submissions/4063218c-6d69-473e-91f3-7d9baf091b2f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- An initial-sigma-algebra conull good-path event permits an all-path adapted regularisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (G : ℝ≥0 → Ω → ℝ)
    (hAdapt : ∀ t, Measurable[𝓕 t] (G t))
    (hZero : ∀ ω, G 0 ω = 0)
    (E : Set Ω)
    (hE : MeasurableSet[𝓕 0] E)
    (hAE : ∀ᵐ ω ∂P, ω ∈ E)
    (hGood : ∀ ω ∈ E, Continuous (fun t : ℝ≥0 => G t ω)) :
    ∃ H : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (H t)) ∧
      (∀ ω, H 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, H t ω = G t ω) ∧
      (∀ ω, Continuous (fun t : ℝ≥0 => H t ω)) := by
  classical
  let H : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ E then G t ω else 0
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · intro t
    have hEt : MeasurableSet[𝓕 t] E :=
      (𝓕.mono (show (0 : ℝ≥0) ≤ t from zero_le)) E hE
    exact Measurable.ite hEt (hAdapt t) measurable_const
  · intro ω
    simp [H, hZero]
  · filter_upwards [hAE] with ω hω
    intro t
    simp [H, hω]
  · intro ω
    by_cases hω : ω ∈ E
    · simpa [H, hω] using hGood ω hω
    · simpa [H, hω] using
        (continuous_const : Continuous (fun _ : ℝ≥0 => (0 : ℝ)))
