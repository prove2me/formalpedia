-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_discrete_stopping_time_inclusive_predictable_mask
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:03:15.382831+00:00
-- url     : https://prove2.me/submissions/402e8e72-acdf-4fb0-8841-1eda3b0be801

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- An inclusive discrete stopping-time mask is predictable for the actual
filtration: at time n+1, survival past n is measurable at n; at time zero
the mask is always one. This is the nonanticipativity ingredient for finite
stopped predictable Poisson grid integrands. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℕ mΩ) (τ : Ω → ℕ)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℕ))) :
    MeasurableSet[𝓕.predictable]
      {p : ℕ × Ω | p.1 ≤ τ p.2} := by
  classical
  have hSlice (n : ℕ) :
      MeasurableSet[𝓕.predictable]
        ({n} ×ˢ {ω : Ω | n ≤ τ ω}) := by
    cases n with
    | zero =>
      have hZero :
          MeasurableSet[𝓕.predictable]
            ({0} ×ˢ (Set.univ : Set Ω)) := by
        apply MeasurableSpace.measurableSet_generateFrom
        exact Or.inl ⟨Set.univ, MeasurableSet.univ, rfl⟩
      simpa only [Nat.zero_le, Set.setOf_true] using hZero
    | succ n =>
      have hLe : MeasurableSet[𝓕 n] {ω : Ω | τ ω ≤ n} := by
        have hCast :
            {ω : Ω | (τ ω : WithTop ℕ) ≤ (n : WithTop ℕ)} =
              {ω : Ω | τ ω ≤ n} := by
          ext ω
          exact (WithTop.coe_le_coe :
            ((τ ω : WithTop ℕ) ≤ (n : WithTop ℕ)) ↔ τ ω ≤ n)
        rw [← hCast]
        exact hτ n
      have hAlive :
          MeasurableSet[𝓕 n] {ω : Ω | n + 1 ≤ τ ω} := by
        have heq :
            {ω : Ω | n + 1 ≤ τ ω} =
              ({ω : Ω | τ ω ≤ n})ᶜ := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
          omega
        rw [heq]
        exact hLe.compl
      have hFuture :
          MeasurableSet[𝓕.predictable]
            (Set.Ioi n ×ˢ {ω : Ω | n + 1 ≤ τ ω}) := by
        apply MeasurableSpace.measurableSet_generateFrom
        exact Or.inr ⟨n, _, hAlive, rfl⟩
      have hLater :
          MeasurableSet[𝓕.predictable]
            (Set.Ioi (n + 1) ×ˢ (Set.univ : Set Ω)) := by
        apply MeasurableSpace.measurableSet_generateFrom
        exact Or.inr ⟨n + 1, Set.univ, MeasurableSet.univ, rfl⟩
      have hSet :
          ({n + 1} ×ˢ {ω : Ω | n + 1 ≤ τ ω}) =
            (Set.Ioi n ×ˢ {ω : Ω | n + 1 ≤ τ ω}) \
              (Set.Ioi (n + 1) ×ˢ (Set.univ : Set Ω)) := by
        ext p
        by_cases ha : n + 1 ≤ τ p.2
        · simp [Set.mem_prod, Set.mem_diff, ha]
          omega
        · have hNot : ¬ n < τ p.2 := by omega
          simp [Set.mem_prod, Set.mem_diff, ha, hNot]
      change MeasurableSet[𝓕.predictable]
        ({n + 1} ×ˢ {ω : Ω | n + 1 ≤ τ ω})
      rw [hSet]
      exact hFuture.diff hLater
  have hEq :
      {p : ℕ × Ω | p.1 ≤ τ p.2} =
        ⋃ n : ℕ, ({n} ×ˢ {ω : Ω | n ≤ τ ω}) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod,
      Set.mem_singleton_iff]
    constructor
    · intro hp
      exact ⟨p.1, rfl, hp⟩
    · rintro ⟨n, hpn, hn⟩
      simpa [hpn] using hn
  rw [hEq]
  exact MeasurableSet.iUnion hSlice
