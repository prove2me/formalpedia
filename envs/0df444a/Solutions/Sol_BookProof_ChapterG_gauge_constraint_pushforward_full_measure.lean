-- Prove2me | solution 1 for BookProof.ChapterG.gauge_constraint_pushforward_full_measure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:18:07.396499+00:00
-- url     : https://prove2.me/submissions/9fae6296-f563-45cd-89ab-0a27b4479840

-- Generated from ChapterG.lean — solution of BookProof.ChapterG.gauge_constraint_pushforward_full_measure
import Mathlib
import Definitions.Def_ChapterG
open MeasureTheory
open BookProof.ChapterG



open scoped ComplexConjugate InnerProductSpace Matrix

variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]

set_option maxHeartbeats 1000000 in
theorem solution
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → X) (hq : Measurable q)
    (C : Set X) (hC : MeasurableSet C)
    (hrange : ∀ x, q x ∈ C) :
    IsProbabilityMeasure (μ.map q) ∧ (μ.map q) C = 1 := by

  refine ⟨Measure.isProbabilityMeasure_map hq.aemeasurable, ?_⟩
  rw [Measure.map_apply hq hC]
  have : q ⁻¹' C = Set.univ := by
    ext x; simp [hrange x]
  rw [this, measure_univ]
