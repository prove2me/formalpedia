-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_rightCont_physical_time_MDS_to_natural_grid_filtration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:42:59.875721+00:00
-- url     : https://prove2.me/submissions/7ec4dc0e-175d-4f9f-9d7c-fcc7826bdee4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_exists_nat_filtration_along_monotone_nonnegative_time_grid
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (s : ℕ → ℝ≥0) (hs : Monotone s)
    (U : ℕ → Ω → ℝ)
    (hAdapt : ∀ i, StronglyMeasurable[𝓕.rightCont (s (i + 1))] (U i))
    (hCenter : ∀ i,
      P[U i | 𝓕.rightCont (s i)] =ᵐ[P] (fun _ => (0 : ℝ))) :
    ∃ 𝓖 : Filtration ℕ mΩ,
      (∀ i, 𝓖 i = 𝓕.rightCont (s i)) ∧
      (∀ i, StronglyMeasurable[𝓖 (i + 1)] (U i)) ∧
      (∀ i, P[U i | 𝓖 i] =ᵐ[P] (fun _ => (0 : ℝ))) := by
  obtain ⟨𝓖, h𝓖⟩ :=
    exists_nat_filtration_along_monotone_nonnegative_time_grid
      𝓕.rightCont s hs
  refine ⟨𝓖, h𝓖, ?_, ?_⟩
  · intro i
    rw [h𝓖]
    exact hAdapt i
  · intro i
    rw [h𝓖]
    exact hCenter i
