-- Prove2me | solution 1 for BookProof.ChapterAbelianCyclicModel.mulRep_toLp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:40:34.571778+00:00
-- url     : https://prove2.me/submissions/e3fbe90a-1708-4009-a10c-af65cb782a50

-- Generated from ChapterAbelianCyclicModel.lean — solution of BookProof.ChapterAbelianCyclicModel.mulRep_toLp
import Mathlib
import Definitions.Def_ChapterAbelianCyclicModel
import Definitions.Def_ChapterAbelianGelfandModel
open BookProof.ChapterAbelianCyclicModel



open MeasureTheory Complex WeakDual
open scoped ComplexOrder


open BookProof.ChapterAbelianGelfandModel


variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H)

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H)
variable (hcyc : DenseRange (repVec pi xi))

set_option maxHeartbeats 1000000 in
theorem solution (g f : C(X, ℂ)) :
    mulRep (repMeasure pi xi) g (ContinuousMap.toLp 2 (repMeasure pi xi) ℂ f)
      = ContinuousMap.toLp 2 (repMeasure pi xi) ℂ (g * f) := by

  set mu := repMeasure pi xi with hmu
  refine Lp.ext ?_
  filter_upwards [mulRep_coeFn mu g (ContinuousMap.toLp 2 mu ℂ f),
    ContinuousMap.coeFn_toLp (p := 2) mu (𝕜 := ℂ) f,
    ContinuousMap.coeFn_toLp (p := 2) mu (𝕜 := ℂ) (g * f)] with x h1 h2 h3
  rw [h1, h2, h3]
  simp
