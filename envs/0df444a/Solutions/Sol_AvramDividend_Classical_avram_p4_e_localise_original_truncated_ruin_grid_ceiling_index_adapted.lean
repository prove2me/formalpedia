-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_truncated_ruin_grid_ceiling_index_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:31:23.348635+00:00
-- url     : https://prove2.me/submissions/389e59de-7daf-4d4c-b3f7-9cea6fc13932

import Mathlib.Probability.Process.Stopping
import Mathlib.Data.Nat.Find
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The least sampled grid point above the exact ruin-truncated clock has adapted events and a uniform finite index bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (N : ℕ) (hN : ∀ ω, τ ω ≤ e N) :
    let cover : ∀ ω, ∃ j : ℕ, τ ω ≤ e j := fun ω => ⟨N, hN ω⟩
    let K : Ω → ℕ := fun ω =>
      @Nat.find (fun j : ℕ => τ ω ≤ e j) (Classical.decPred (fun j : ℕ => τ ω ≤ e j)) (cover ω)
    (∀ i, MeasurableSet[𝓕.rightCont (e i)] {ω : Ω | K ω ≤ i}) ∧
      (∀ ω, K ω ≤ N) := by
  classical
  let cover : ∀ ω, ∃ j : ℕ, τ ω ≤ e j := fun ω => ⟨N, hN ω⟩
  let K : Ω → ℕ := fun ω =>
    @Nat.find (fun j : ℕ => τ ω ≤ e j) (Classical.decPred (fun j : ℕ => τ ω ≤ e j)) (cover ω)
  change (∀ i, MeasurableSet[𝓕.rightCont (e i)] {ω : Ω | K ω ≤ i}) ∧
    (∀ ω, K ω ≤ N)
  have hKiff (ω : Ω) (i : ℕ) : K ω ≤ i ↔ τ ω ≤ e i := by
    constructor
    · intro hi
      have hs : τ ω ≤ e (K ω) := Nat.find_spec (cover ω)
      exact hs.trans (he hi)
    · intro hi
      apply (Nat.find_le_iff (cover ω) i).2
      exact ⟨i, le_rfl, hi⟩
  constructor
  · intro i
    have hm : MeasurableSet[𝓕.rightCont (e i)]
        {ω : Ω | τ ω ≤ e i} := by
      simpa only [WithTop.coe_le_coe] using hτstop (e i)
    have hSet : {ω : Ω | K ω ≤ i} = {ω : Ω | τ ω ≤ e i} := by
      ext ω
      exact hKiff ω i
    rw [hSet]
    exact hm
  · intro ω
    exact (hKiff ω N).2 (hN ω)
