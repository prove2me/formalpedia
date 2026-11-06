-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_run1640_rightcont_physical_completed_cell_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:56:07.472203+00:00
-- url     : https://prove2.me/submissions/b5a74041-1c8c-40da-852c-d8776ffd780a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- A genuinely adapted physical count and predictable weight give a completed-grid adapted compensated cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (H N D : ℕ → Ω → ℝ) (r : ℕ → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (hN : ∀ i,
      StronglyMeasurable[𝓕.rightCont (grid (i + 1))] (N i))
    (hD : ∀ i ω, D i ω = H i ω * (N i ω - r i)) :
    ∀ i, StronglyMeasurable[𝓕.rightCont (grid (i + 1))] (D i) := by
  intro i
  have hTime : grid i ≤ grid (i + 1) := hGrid i
  have hHnext : StronglyMeasurable[𝓕.rightCont (grid (i + 1))] (H i) :=
    (hH i).mono ((𝓕.rightCont).mono hTime)
  have hNnext : StronglyMeasurable[𝓕.rightCont (grid (i + 1))]
      (fun ω => N i ω - r i) :=
    (hN i).sub stronglyMeasurable_const
  have hProduct : StronglyMeasurable[𝓕.rightCont (grid (i + 1))]
      (fun ω => H i ω * (N i ω - r i)) :=
    hHnext.mul hNnext
  have hIdentity : D i = fun ω => H i ω * (N i ω - r i) :=
    funext (hD i)
  rw [hIdentity]
  exact hProduct
