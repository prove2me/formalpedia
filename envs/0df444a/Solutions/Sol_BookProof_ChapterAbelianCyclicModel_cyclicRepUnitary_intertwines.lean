-- Prove2me | solution 1 for BookProof.ChapterAbelianCyclicModel.cyclicRepUnitary_intertwines
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:40:35.664184+00:00
-- url     : https://prove2.me/submissions/315e0d4a-accf-40b9-81ec-843c8cc7ecd9

-- Generated from ChapterAbelianCyclicModel.lean — solution of BookProof.ChapterAbelianCyclicModel.cyclicRepUnitary_intertwines
import Mathlib
import Definitions.Def_ChapterAbelianCyclicModel
import Theorems.Thm_BookProof_ChapterAbelianCyclicModel_mulRep_toLp
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
theorem solution (g : C(X, ℂ)) (u : Lp ℂ 2 (repMeasure pi xi)) :
    cyclicRepUnitary pi xi hcyc (mulRep (repMeasure pi xi) g u)
      = pi g (cyclicRepUnitary pi xi hcyc u) := by

  have hdense : DenseRange
      ((ContinuousMap.toLp 2 (repMeasure pi xi) ℂ).toLinearMap :
        C(X, ℂ) → Lp ℂ 2 (repMeasure pi xi)) :=
    ContinuousMap.toLp_denseRange ℂ _ (μ := repMeasure pi xi) (by simp)
  have hcont₁ : Continuous fun v : Lp ℂ 2 (repMeasure pi xi) =>
      cyclicRepUnitary pi xi hcyc (mulRep (repMeasure pi xi) g v) :=
    (cyclicRepUnitary pi xi hcyc).continuous.comp (mulRep (repMeasure pi xi) g).continuous
  have hcont₂ : Continuous fun v : Lp ℂ 2 (repMeasure pi xi) =>
      pi g (cyclicRepUnitary pi xi hcyc v) :=
    (pi g).continuous.comp (cyclicRepUnitary pi xi hcyc).continuous
  have hfun : (fun v : Lp ℂ 2 (repMeasure pi xi) =>
        cyclicRepUnitary pi xi hcyc (mulRep (repMeasure pi xi) g v))
      = fun v : Lp ℂ 2 (repMeasure pi xi) => pi g (cyclicRepUnitary pi xi hcyc v) := by
    refine hdense.equalizer hcont₁ hcont₂ (funext fun f => ?_)
    simp only [Function.comp_apply, ContinuousLinearMap.coe_coe]
    rw [mulRep_toLp pi xi g f, cyclicRepUnitary_toLp, cyclicRepUnitary_toLp, map_mul]
    rfl
  exact congrFun hfun u
