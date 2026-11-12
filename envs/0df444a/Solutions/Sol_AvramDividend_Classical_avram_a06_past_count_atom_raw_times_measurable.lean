-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_past_count_atom_raw_times_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:54:44.717798+00:00
-- url     : https://prove2.me/submissions/ab52a14d-6d0c-4308-b1f2-7d42e05c6df8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_past_count_atom_history_comap_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

/-- Endpoints outside the finite past prefix are clamped to the history clock. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (N : Ω → ℝ → ℕ) (clock : ℝ)
    (n : ℕ) (a b : Fin n → ℝ) (j : Fin n) (v : Fin n → ℕ)
    (ha : ∀ i : Fin n, i < j → a i ≤ clock)
    (hb : ∀ i : Fin n, i < j → b i ≤ clock) :
    MeasurableSet[
      MeasurableSpace.comap
        (fun ω : Ω => fun s : Set.Iic clock => N ω (s : ℝ))
        (inferInstance : MeasurableSpace (Set.Iic clock → ℕ))]
      {ω | ∀ i : Fin n, i < j →
        N ω (b i) - N ω (a i) = v i} := by
  classical
  let aa : Fin n → Set.Iic clock := fun i =>
    if hi : i < j then ⟨a i, ha i hi⟩ else ⟨clock, by simp⟩
  let bb : Fin n → Set.Iic clock := fun i =>
    if hi : i < j then ⟨b i, hb i hi⟩ else ⟨clock, by simp⟩
  have h := AvramDividend.Classical.avram_a06_past_count_atom_history_comap_measurable
    N clock n aa bb j v
  have hSet :
      {ω | ∀ i : Fin n, i < j → N ω (b i) - N ω (a i) = v i} =
      {ω | ∀ i : Fin n, i < j →
        N ω (bb i : ℝ) - N ω (aa i : ℝ) = v i} := by
    ext ω
    constructor
    · intro hω i hi
      simpa [aa, bb, hi] using hω i hi
    · intro hω i hi
      simpa [aa, bb, hi] using hω i hi
  rw [hSet]
  exact h
