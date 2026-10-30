-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_random_grid_killed_history_meas
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:46:22.97499+00:00
-- url     : https://prove2.me/submissions/2a83f9a8-5f97-4eec-ad2f-beadfdeb6239

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- An original-Levy closed-history killing event at a measurable random
grid clock is measurable if each deterministic-clock killed event is. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (clock : ℕ → ℝ≥0) (K : Ω → ℕ)
    (hKm : Measurable K)
    (hHistory : ∀ k : ℕ, MeasurableSet
      {ω : Ω | ∀ t : ℝ≥0, t ≤ clock k →
        0 ≤ x + X.X t ω}) :
    MeasurableSet {ω : Ω | ∀ t : ℝ≥0,
      t ≤ clock (K ω) → 0 ≤ x + X.X t ω} := by
  let B : ℕ → Set Ω := fun k =>
    {ω : Ω | ∀ t : ℝ≥0, t ≤ clock k → 0 ≤ x + X.X t ω}
  have hEq : {ω : Ω | ∀ t : ℝ≥0,
      t ≤ clock (K ω) → 0 ≤ x + X.X t ω} =
      ⋃ k : ℕ, {ω : Ω | K ω = k} ∩ B k := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, B]
    constructor
    · intro h
      exact ⟨K ω, rfl, h⟩
    · rintro ⟨k, hKk, hBk⟩
      simpa [hKk] using hBk
  rw [hEq]
  exact MeasurableSet.iUnion fun k =>
    ((measurableSet_singleton k).preimage hKm).inter (hHistory k)
