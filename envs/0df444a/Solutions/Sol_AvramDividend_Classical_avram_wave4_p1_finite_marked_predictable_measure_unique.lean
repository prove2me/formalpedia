-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_finite_marked_predictable_measure_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:09:39.541753+00:00
-- url     : https://prove2.me/submissions/eb19bb46-9303-4719-80b2-91d8159aa87a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_measure_unique_from_rectangles

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

/-- Equality on elementary past/mark rectangles determines a finite measure
on the complete predictable-by-mark measurable space. -/
theorem solution
    {Ω E ι : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    [LinearOrder ι] [OrderBot ι]
    (𝓕 : Filtration ι mΩ)
    (M N : @Measure ((ι × Ω) × E)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable) mE))
    [IsFiniteMeasure M]
    (hBot : ∀ (A : Set Ω) (B : Set E),
      MeasurableSet[𝓕 ⊥] A → MeasurableSet B →
      M (({(⊥ : ι)} ×ˢ A) ×ˢ B) =
        N (({(⊥ : ι)} ×ˢ A) ×ˢ B))
    (hFuture : ∀ (i : ι) (A : Set Ω) (B : Set E),
      MeasurableSet[𝓕 i] A → MeasurableSet B →
      M ((Set.Ioi i ×ˢ A) ×ˢ B) =
        N ((Set.Ioi i ×ˢ A) ×ˢ B)) :
    M = N := by
  classical
  letI : MeasurableSpace (ι × Ω) := 𝓕.predictable
  letI : MeasurableSpace ((ι × Ω) × E) := Prod.instMeasurableSpace
  have hMarg (Q : Measure ((ι × Ω) × E)) (B : Set E)
      (hB : MeasurableSet B) (S : Set (ι × Ω)) (hS : MeasurableSet S) :
      ((Q.restrict (Set.univ ×ˢ B)).map Prod.fst) S = Q (S ×ˢ B) := by
    rw [Measure.map_apply measurable_fst hS]
    have hPre : Prod.fst ⁻¹' S = S ×ˢ (Set.univ : Set E) := by
      ext ⟨x, y⟩
      simp [Set.mem_prod]
    rw [hPre, Measure.restrict_apply (hS.prod MeasurableSet.univ)]
    congr 1
    ext ⟨x, y⟩
    simp [Set.mem_prod]
  refine Measure.ext_prod ?_
  intro S B hS hB
  let MB : Measure (ι × Ω) :=
    (M.restrict (Set.univ ×ˢ B)).map Prod.fst
  let NB : Measure (ι × Ω) :=
    (N.restrict (Set.univ ×ˢ B)).map Prod.fst
  have hMB (T : Set (ι × Ω)) (hT : MeasurableSet T) :
      MB T = M (T ×ˢ B) := hMarg M B hB T hT
  have hNB (T : Set (ι × Ω)) (hT : MeasurableSet T) :
      NB T = N (T ×ˢ B) := hMarg N B hB T hT
  have hMBfinite : MB Set.univ ≠ ∞ := by
    rw [hMB Set.univ MeasurableSet.univ]
    exact (measure_lt_top M (Set.univ ×ˢ B)).ne
  have hBotMB : ∀ A : Set Ω, MeasurableSet[𝓕 ⊥] A →
      MB ({(⊥ : ι)} ×ˢ A) = NB ({(⊥ : ι)} ×ˢ A) := by
    intro A hA
    have hS : MeasurableSet[𝓕.predictable] ({(⊥ : ι)} ×ˢ A) :=
      measurableSet_predictable_singleton_bot_prod hA
    rw [hMB _ hS, hNB _ hS]
    exact hBot A B hA hB
  have hFutureMB : ∀ i : ι, ∀ A : Set Ω, MeasurableSet[𝓕 i] A →
      MB (Set.Ioi i ×ˢ A) = NB (Set.Ioi i ×ˢ A) := by
    intro i A hA
    have hS : MeasurableSet[𝓕.predictable] (Set.Ioi i ×ˢ A) :=
      measurableSet_predictable_Ioi_prod hA
    rw [hMB _ hS, hNB _ hS]
    exact hFuture i A B hA hB
  have hEq : MB = NB :=
    AvramDividend.Classical.avram_wave4_p1_predictable_measure_unique_from_rectangles
      𝓕 MB NB hMBfinite hBotMB hFutureMB
  calc
    M (S ×ˢ B) = MB S := (hMB S hS).symm
    _ = NB S := by rw [hEq]
    _ = N (S ×ˢ B) := hNB S hS
