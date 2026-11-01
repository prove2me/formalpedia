-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_sigma_finite_marked_predictable_measure_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:30:38.708408+00:00
-- url     : https://prove2.me/submissions/725ffd00-2f84-449a-b64f-5ee22efc3835

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_marked_predictable_measure_unique

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
theorem solution
    {Ω E ι : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    [LinearOrder ι] [OrderBot ι]
    (𝓕 : Filtration ι mΩ)
    (M N : @Measure ((ι × Ω) × E) (@Prod.instMeasurableSpace _ _ (𝓕.predictable) mE))
    (B : ℕ → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBmono : Monotone B) (hBcover : (⋃ k, B k) = Set.univ)
    (hLocal : ∀ k, M ((Set.univ : Set (ι × Ω)) ×ˢ B k) ≠ ∞)
    (hBot : ∀ (A : Set Ω) (C : Set E),
      MeasurableSet[𝓕 ⊥] A → MeasurableSet C →
      M (({(⊥ : ι)} ×ˢ A) ×ˢ C) = N (({(⊥ : ι)} ×ˢ A) ×ˢ C))
    (hFuture : ∀ (i : ι) (A : Set Ω) (C : Set E),
      MeasurableSet[𝓕 i] A → MeasurableSet C →
      M ((Set.Ioi i ×ˢ A) ×ˢ C) = N ((Set.Ioi i ×ˢ A) ×ˢ C)) :
    M = N := by
  classical
  letI : MeasurableSpace (ι × Ω) := 𝓕.predictable
  letI : MeasurableSpace ((ι × Ω) × E) := Prod.instMeasurableSpace
  have hRestr (k : ℕ) :
      M.restrict (Set.univ ×ˢ B k) = N.restrict (Set.univ ×ˢ B k) := by
    letI : IsFiniteMeasure (M.restrict (Set.univ ×ˢ B k)) := ⟨by simpa [Measure.restrict_apply] using
        (lt_top_iff_ne_top.mpr (hLocal k))⟩
    have hSlice (T : Set (ι × Ω))
        (hT : MeasurableSet[𝓕.predictable] T)
        (C : Set E) (hC : MeasurableSet C)
        (hEq : ∀ D : Set E, MeasurableSet D →
          M (T ×ˢ D) = N (T ×ˢ D)) :
        (M.restrict (Set.univ ×ˢ B k)) (T ×ˢ C) =
          (N.restrict (Set.univ ×ˢ B k)) (T ×ˢ C) := by
      have hTC : MeasurableSet (T ×ˢ C) := hT.prod hC
      rw [Measure.restrict_apply hTC, Measure.restrict_apply hTC]
      have hInter : (T ×ˢ C) ∩ (Set.univ ×ˢ B k) =
          T ×ˢ (C ∩ B k) := by
        ext ⟨x, z⟩
        simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and]
        tauto
      rw [hInter]
      exact hEq (C ∩ B k) (hC.inter (hBm k))
    apply AvramDividend.Classical.avram_wave4_p1_finite_marked_predictable_measure_unique
      𝓕 (M.restrict (Set.univ ×ˢ B k))
      (N.restrict (Set.univ ×ˢ B k))
    · intro A C hA hC
      exact hSlice ({(⊥ : ι)} ×ˢ A)
        (measurableSet_predictable_singleton_bot_prod hA)
        C hC (fun D hD => hBot A D hA hD)
    · intro i A C hA hC
      exact hSlice (Set.Ioi i ×ˢ A)
        (measurableSet_predictable_Ioi_prod hA)
        C hC (fun D hD => hFuture i A D hA hD)
  ext S hS
  let F : ℕ → Set ((ι × Ω) × E) := fun k => S ∩ (Set.univ ×ˢ B k)
  have hm : Monotone F := by
    intro i j hij p hp
    exact ⟨hp.1, ⟨hp.2.1, hBmono hij hp.2.2⟩⟩
  have hCover : (⋃ k, F k) = S := by
    ext ⟨x, z⟩
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      exact hk.1
    · intro hx
      have hz : z ∈ ⋃ k, B k := by rw [hBcover]; trivial
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_iUnion.mpr ⟨k, hx, by simp [F, hk]⟩
  calc
    M S = M (⋃ k, F k) := by rw [hCover]
    _ = ⨆ k, M (F k) := hm.measure_iUnion
    _ = ⨆ k, N (F k) := by
      apply iSup_congr
      intro k
      have hk := congrArg (fun Q : Measure ((ι × Ω) × E) => Q S) (hRestr k)
      simpa only [Measure.restrict_apply hS, F] using hk
    _ = N (⋃ k, F k) := (hm.measure_iUnion).symm
    _ = N S := by rw [hCover]
