-- Prove2me | solution 1 for AvramDividend.Classical.esscher_finite_grid_stop_likelihood_observable_map_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:43:41.845952+00:00
-- url     : https://prove2.me/submissions/262782e7-4bc0-464d-b1eb-81d544d71ca9

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_likelihood_history
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [mα : MeasurableSpace α]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T : ℝ≥0) (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hT : ∀ s ∈ grid, s ≤ T)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s})
    (Z : Ω → α)
    (hZhistory : ∀ s ∈ grid, ∀ B : Set α, MeasurableSet B →
      MeasurableSet[𝓕 s] (Z ⁻¹' B ∩ {ω : Ω | τ ω = s})) :
    Measure.map Z
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) =
    Measure.map Z
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)))) := by
  classical
  have hZm : Measurable Z := by
    intro B hB
    have hcover : Z ⁻¹' B =
        ⋃ s ∈ grid, Z ⁻¹' B ∩ {ω : Ω | τ ω = s} := by
      ext ω
      simp only [Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_setOf_eq, Set.mem_preimage, exists_prop]
      constructor
      · intro hz
        exact ⟨τ ω, hgrid ω, hz, rfl⟩
      · rintro ⟨s, -, hz, -⟩
        exact hz
    rw [hcover]
    apply Finset.measurableSet_biUnion
    intro s hs
    exact 𝓕.le s _ (hZhistory s hs B hB)
  ext B hB
  rw [Measure.map_apply hZm hB, Measure.map_apply hZm hB]
  exact esscher_finite_grid_stop_likelihood_history
    X θ hθ T τ grid hgrid hT hstop (Z ⁻¹' B) (hZm hB)
      (fun s hs => hZhistory s hs B hB)
