-- Prove2me | solution 1 for BookProof.ChapterPvmScalarMeasure.exists_quasiInvariant_scalarMeasure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T09:57:04.089758+00:00
-- url     : https://prove2.me/submissions/486ae575-4409-42b1-b3cb-81c0dffdc68e

-- Generated from ChapterPvmScalarMeasure.lean — solution of BookProof.ChapterPvmScalarMeasure.exists_quasiInvariant_scalarMeasure
import Mathlib
import Definitions.Def_ChapterPvmScalarMeasure
import Theorems.Thm_BookProof_ChapterPvmScalarMeasure_quasiInvariant_of_null_iff
import Definitions.Def_ChapterPvmMeasure
import Definitions.Def_ChapterPvmCyclicDecomposition
import Definitions.Def_ChapterMackeyConverse
import Definitions.Def_ChapterPvmInducedSystem
import Definitions.Def_ChapterMackeyQuasiInvariant
open BookProof.ChapterPvmScalarMeasure



open MeasureTheory
open scoped InnerProductSpace


open BookProof.ChapterPvmMeasure BookProof.ChapterPvmCyclicDecomposition
open BookProof.ChapterMackeyQuasiInvariant BookProof.ChapterMackeyConverse
open BookProof.ChapterPvmInducedSystem
open BookProof.ChapterMackeyQuasiInvariant

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {G : Type*} [Group G] [MulAction G X]

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (T : ContinuousImprimitivitySystem G X H) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ QuasiInvariant μ G ∧
      ∀ E : Set X, MeasurableSet E → (μ E = 0 ↔ T.P.p E = 0) := by

  obtain ⟨μ, hfin, hnull⟩ := exists_scalarMeasure T.P
  exact ⟨μ, hfin, quasiInvariant_of_null_iff T hnull, hnull⟩
