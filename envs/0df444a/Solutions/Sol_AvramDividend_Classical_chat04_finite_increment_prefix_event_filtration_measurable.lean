-- Prove2me | solution 1 for AvramDividend.Classical.chat04_finite_increment_prefix_event_filtration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:42:22.618048+00:00
-- url     : https://prove2.me/submissions/a9724e27-48aa-4ce0-bb16-663b3e6d33f7

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Uniform measurability of the joint event for ANY finite prefix of
consecutive Lévy increments. Every observed increment ends by t n,
so the complete conjunction belongs to F_(t n), allowing induction
on the probability of successive increment-cylinder restrictions.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℕ → ℝ≥0) (ht : Monotone t)
    (n : ℕ) (B : ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i)) :
    MeasurableSet[𝓕 (t n)]
      {ω | ∀ i : ℕ, i < n →
        X.X (t (i + 1)) ω - X.X (t i) ω ∈ B i} := by
  let D : ℕ → Set Ω :=
    fun i => {ω | i < n →
      X.X (t (i + 1)) ω - X.X (t i) ω ∈ B i}
  have hD : ∀ i, MeasurableSet[𝓕 (t n)] (D i) := by
    intro i
    by_cases hi : i < n
    · have hti : t i ≤ t n := ht (Nat.le_of_lt hi)
      have hti1 : t (i + 1) ≤ t n := ht (Nat.succ_le_of_lt hi)
      have hXi : Measurable[𝓕 (t n)] (X.X (t i)) :=
        (X.adapted (t i)).mono (𝓕.mono hti) le_rfl
      have hXi1 : Measurable[𝓕 (t n)] (X.X (t (i + 1))) :=
        (X.adapted (t (i + 1))).mono (𝓕.mono hti1) le_rfl
      have hEv : MeasurableSet[𝓕 (t n)]
          {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B i} :=
        (hB i).preimage (hXi1.sub hXi)
      simpa [D, hi] using hEv
    · have heq : D i = Set.univ := by
        ext ω
        simp [D, hi]
      rw [heq]
      exact MeasurableSet.univ
  have hInt : MeasurableSet[𝓕 (t n)] (⋂ i, D i) :=
    MeasurableSet.iInter hD
  have heq :
      {ω | ∀ i : ℕ, i < n →
        X.X (t (i + 1)) ω - X.X (t i) ω ∈ B i} =
        ⋂ i, D i := by
    ext ω
    simp [D]
  rw [heq]
  exact hInt
