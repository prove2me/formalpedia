-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_predictable_measure_unique_from_rectangles
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:59:08.575825+00:00
-- url     : https://prove2.me/submissions/45918eee-72fb-43ef-9aa4-8ce20cdadd37

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
/-- Equality on predictable generating rectangles determines a finite measure. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι]
    (𝓕 : Filtration ι mΩ)
    (μ ν : @Measure (ι × Ω) (𝓕.predictable))
    (hFinite : μ Set.univ ≠ ∞)
    (hBot : ∀ A : Set Ω, MeasurableSet[𝓕 ⊥] A → μ ({(⊥ : ι)} ×ˢ A) = ν ({(⊥ : ι)} ×ˢ A))
    (hFuture : ∀ i : ι, ∀ A : Set Ω, MeasurableSet[𝓕 i] A → μ (Set.Ioi i ×ˢ A) = ν (Set.Ioi i ×ˢ A)) :
    μ = ν := by
  classical
  letI : MeasurableSpace (ι × Ω) := 𝓕.predictable
  let G : Set (Set (ι × Ω)) :=
    {s | ∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
      s = {(⊥ : ι)} ×ˢ A} ∪
    {s | ∃ i : ι, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
      s = Set.Ioi i ×ˢ A}
  have hGen : 𝓕.predictable = MeasurableSpace.generateFrom G := rfl
  have hPi : IsPiSystem G := by
    intro u hu v hv hne
    rcases hu with ⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩
    · rcases hv with ⟨B, hB, rfl⟩ | ⟨j, B, hB, rfl⟩
      · left
        refine ⟨A ∩ B, hA.inter hB, ?_⟩
        ext ⟨k, ω⟩; simp only [Set.mem_prod, Set.mem_inter_iff, Set.mem_singleton_iff]; tauto
      · exfalso
        obtain ⟨⟨k, ω⟩, hk⟩ := hne
        simp only [Set.mem_inter_iff, Set.mem_prod,
          Set.mem_singleton_iff, Set.mem_Ioi] at hk
        have hj : j < (⊥ : ι) := by simpa [hk.1.1] using hk.2.1
        exact (not_lt_of_ge bot_le) hj
    · rcases hv with ⟨B, hB, rfl⟩ | ⟨j, B, hB, rfl⟩
      · exfalso
        obtain ⟨⟨k, ω⟩, hk⟩ := hne
        simp only [Set.mem_inter_iff, Set.mem_prod,
          Set.mem_singleton_iff, Set.mem_Ioi] at hk
        have hi : i < (⊥ : ι) := by simpa [hk.2.1] using hk.1.1
        exact (not_lt_of_ge bot_le) hi
      · right
        refine ⟨max i j, A ∩ B,
          (𝓕.mono (le_max_left i j) _ hA).inter
            (𝓕.mono (le_max_right i j) _ hB), ?_⟩
        ext ⟨k, ω⟩
        simp only [Set.mem_inter_iff, Set.mem_prod,
          Set.mem_Ioi, max_lt_iff]
        tauto
  let B : ℕ → Set (ι × Ω) := fun n =>
    if n = 0 then {(⊥ : ι)} ×ˢ (Set.univ : Set Ω)
    else Set.Ioi (⊥ : ι) ×ˢ (Set.univ : Set Ω)
  have hBmem : ∀ n, B n ∈ G := by
    intro n
    by_cases hn : n = 0
    · left
      refine ⟨Set.univ, MeasurableSet.univ, ?_⟩
      simp [B, hn]
    · right
      refine ⟨⊥, Set.univ, MeasurableSet.univ, ?_⟩
      simp [B, hn]
  have hCover : (⋃ n, B n) = Set.univ := by
    ext ⟨k, ω⟩
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hk : k = ⊥
    · refine ⟨0, ?_⟩
      simp [B, hk]
    · refine ⟨1, ?_⟩
      have hlt : (⊥ : ι) < k := lt_of_le_of_ne bot_le (Ne.symm hk)
      simp [B, hlt]
  have hBfinite : ∀ n, μ (B n) ≠ ∞ := by
    intro n; exact ne_top_of_le_ne_top hFinite (measure_mono (Set.subset_univ _))
  have hEq : ∀ s ∈ G, μ s = ν s := by
    intro s hs
    rcases hs with ⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩
    · exact hBot A hA
    · exact hFuture i A hA
  exact Measure.ext_of_generateFrom_of_iUnion G B hGen hPi hCover hBmem hBfinite hEq
