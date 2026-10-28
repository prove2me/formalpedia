-- Prove2me | solution 1 for AvramDividend.Classical.stoppedHistory_event_probability_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:22:06.563003+00:00
-- url     : https://prove2.me/submissions/5e12b32a-f1e1-42a4-9713-7a7090387117

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Algebra.Order.Archimedean.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- The probability of a stopped-history event is exhausted by finite horizons. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (τ : Ω → ℝ≥0) (A : Set Ω) :
    Tendsto
      (fun n : ℕ => P (A ∩ {ω : Ω | τ ω ≤ (n : ℝ≥0)}))
      atTop (nhds (P A)) := by
  let E : ℕ → Set Ω :=
    fun n => A ∩ {ω : Ω | τ ω ≤ (n : ℝ≥0)}
  have hmono : Monotone E := by
    intro n m hnm
    intro ω hω
    change ω ∈ A ∩ {ω' : Ω | τ ω' ≤ (n : ℝ≥0)} at hω
    change ω ∈ A ∩ {ω' : Ω | τ ω' ≤ (m : ℝ≥0)}
    refine ⟨hω.1, ?_⟩
    have hcast : (n : ℝ≥0) ≤ (m : ℝ≥0) := by
      exact_mod_cast hnm
    exact hω.2.trans hcast
  have hunion : (⋃ n, E n) = A := by
    ext ω
    constructor
    · intro hω
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hω
      exact hn.1
    · intro hω
      obtain ⟨n, hn⟩ : ∃ n : ℕ, τ ω ≤ (n : ℝ≥0) :=
        exists_nat_ge (τ ω)
      exact Set.mem_iUnion.mpr ⟨n, ⟨hω, hn⟩⟩
  have hlim := tendsto_measure_iUnion_atTop (μ := P) hmono
  simpa only [Function.comp_def, E, hunion] using hlim
