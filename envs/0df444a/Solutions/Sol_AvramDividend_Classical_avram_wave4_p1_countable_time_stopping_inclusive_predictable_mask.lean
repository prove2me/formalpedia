-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_countable_time_stopping_inclusive_predictable_mask
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T18:56:09.711575+00:00
-- url     : https://prove2.me/submissions/d2bae0e6-1f5c-4743-905f-36331cda7d4f

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- On any linearly ordered time set admitting a countable family that
separates ordered pairs from the right, the inclusive stopped survival mask
is genuinely predictable for the original filtration. For nonnegative real
time, one may choose nonnegative rational times as the separating family.
The identity uses original stopping-time past events and does not assume a
compensator, a Campbell formula or a martingale conclusion. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι]
    (𝓕 : Filtration ι mΩ)
    (D : Set ι) (hD : D.Countable)
    (hSep : ∀ a b : ι, a < b →
      ∃ s : ι, s ∈ D ∧ a ≤ s ∧ s < b)
    (τ : Ω → ι)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ι))) :
    MeasurableSet[𝓕.predictable]
      {p : ι × Ω | p.1 ≤ τ p.2} := by
  classical
  let Q (s : ι) : Set (ι × Ω) :=
    (Set.Iic s ×ˢ (Set.univ : Set Ω)) ∪
    (Set.Ioi s ×ˢ {ω : Ω | s < τ ω})
  have hQ (s : ι) : MeasurableSet[𝓕.predictable] (Q s) := by
    have hStop : MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s} := by
      simpa only [WithTop.coe_le_coe] using (hτ s)
    have hAlive : MeasurableSet[𝓕 s] {ω : Ω | s < τ ω} := by
      have heq : {ω : Ω | s < τ ω} =
          ({ω : Ω | τ ω ≤ s})ᶜ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
      rw [heq]
      exact hStop.compl
    have hBefore :
        MeasurableSet[𝓕.predictable]
          (Set.Iic s ×ˢ (Set.univ : Set Ω)) := by
      have hFutureAll :
          MeasurableSet[𝓕.predictable]
            (Set.Ioi s ×ˢ (Set.univ : Set Ω)) :=
        measurableSet_predictable_Ioi_prod (𝓕 := 𝓕) MeasurableSet.univ
      have heq :
          Set.Iic s ×ˢ (Set.univ : Set Ω) =
          (Set.Ioi s ×ˢ (Set.univ : Set Ω))ᶜ := by
        ext p
        simp only [Set.mem_prod, Set.mem_Iic, Set.mem_Ioi,
          Set.mem_univ, and_true, Set.mem_compl_iff, not_lt]
      rw [heq]
      exact hFutureAll.compl
    have hAfter :
        MeasurableSet[𝓕.predictable]
          (Set.Ioi s ×ˢ {ω : Ω | s < τ ω}) :=
      measurableSet_predictable_Ioi_prod (𝓕 := 𝓕) hAlive
    exact hBefore.union hAfter
  have hEq :
      {p : ι × Ω | p.1 ≤ τ p.2} = ⋂ s ∈ D, Q s := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hp s hs
      change p ∈
        (Set.Iic s ×ˢ (Set.univ : Set Ω)) ∪
        (Set.Ioi s ×ˢ {ω : Ω | s < τ ω})
      by_cases hps : p.1 ≤ s
      · exact Or.inl ⟨hps, Set.mem_univ _⟩
      · have hsp : s < p.1 := lt_of_not_ge hps
        exact Or.inr ⟨hsp, lt_of_lt_of_le hsp hp⟩
    · intro hp
      by_contra hbad
      have hlt : τ p.2 < p.1 := lt_of_not_ge hbad
      obtain ⟨s, hsD, hslo, hshi⟩ :=
        hSep (τ p.2) p.1 hlt
      have hmem : p ∈ Q s := hp s hsD
      change p ∈
        (Set.Iic s ×ˢ (Set.univ : Set Ω)) ∪
        (Set.Ioi s ×ˢ {ω : Ω | s < τ ω}) at hmem
      rcases hmem with hleft | hright
      · exact (not_le_of_gt hshi) hleft.1
      · exact (not_lt_of_ge hslo) hright.2
  rw [hEq]
  exact MeasurableSet.biInter hD (fun s _ => hQ s)
