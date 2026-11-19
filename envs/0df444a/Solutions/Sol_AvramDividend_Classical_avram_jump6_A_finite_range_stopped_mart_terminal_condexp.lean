-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_finite_range_stopped_mart_terminal_condexp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:42:37.914052+00:00
-- url     : https://prove2.me/submissions/5e578a87-e466-4034-b806-10db69f55dd4

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (G : ℝ≥0 → Ω → ℝ)
    (hAdapted : ∀ t : ℝ≥0, Measurable[𝓕.rightCont t] (G t))
    (hInt : ∀ t : ℝ≥0, Integrable (G t) P)
    (hCond : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (G t) ω = G s ω)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hBound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hS : ∀ ω, ρ ω ∈ S) :
    (fun ω => G (ρ ω) ω) =ᵐ[P]
      condExp hStop.measurableSpace P (G (n : ℝ≥0)) := by
  classical
  have hMart : Martingale G 𝓕.rightCont P := by
    constructor
    · intro t
      exact (hAdapted t).stronglyMeasurable
    · intro s t hst
      exact hCond s t hst
  have hRangeCountable :
      (Set.range (fun ω : Ω => (ρ ω : WithTop ℝ≥0))).Countable := by
    have hf : (Set.range (fun ω : Ω => (ρ ω : WithTop ℝ≥0))).Finite := by
      apply ((Finset.finite_toSet S).image
        (fun t : ℝ≥0 => (t : WithTop ℝ≥0))).subset
      rintro y ⟨ω, rfl⟩
      exact ⟨ρ ω, hS ω, rfl⟩
    exact hf.countable
  have hLe : ∀ ω, (ρ ω : WithTop ℝ≥0) ≤ (n : WithTop ℝ≥0) := by
    intro ω
    exact_mod_cast hBound ω
  have h :=
    hMart.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
      hStop hLe hRangeCountable
  exact h
