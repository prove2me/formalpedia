-- Prove2me | solution 1 for BookProof.ChapterSeparableL2Model.abelian_multiplication_model_classified_separable_hilbert
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-06T12:37:17.436938+00:00
-- url     : https://prove2.me/submissions/a6122bbe-7062-4658-b1fd-f654a732b80b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSeparableL2Model.lean — solution of BookProof.ChapterSeparableL2Model.abelian_multiplication_model_classified_separable_hilbert
import Mathlib
import Definitions.Def_ChapterSeparableL2Model
import Theorems.Thm_BookProof_ChapterSeparableL2Model_separable_Lp_realizes_standard_type
import Theorems.Thm_BookProof_ChapterSeparableL2Model_separableSpace_of_linearIsometry
import Theorems.Thm_BookProof_ChapterAbelianCyclicModel_isProbabilityMeasure_repMeasure
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterAbelianCyclicModel
import Definitions.Def_ChapterAbelianDirectSum
import Definitions.Def_ChapterStandardBorelClassification
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterSeparableL2Model



universe u

noncomputable section

open MeasureTheory TopologicalSpace


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterAbelianCyclicModel
open BookProof.ChapterAbelianDirectSum BookProof.ChapterLinftyMultiplication
open BookProof.ChapterStandardBorelClassification
open BookProof.ChapterLinftyMultiplication

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] (mu : Measure Y) [IsFiniteMeasure mu] [mu.WeaklyRegular]
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y]
  [BorelSpace Y] (D : Set C(Y, ℂ)) [Countable D]
variable {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] (mu : Measure Y) [IsProbabilityMeasure mu] [mu.WeaklyRegular]
variable {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in
theorem solution [SeparableSpace H]
    (pi : C(Y, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    ∃ (S : Set H) (mu : S → Measure Y) (V : ∀ x : S, Lp ℂ 2 (mu x) →ₗᵢ[ℂ] H),
      S.Countable ∧
      (∀ x : S, IsProbabilityMeasure (mu x)) ∧
      IsHilbertSum ℂ (fun x : S => Lp ℂ 2 (mu x)) V ∧
      (∀ (x : S) (g : C(Y, ℂ)) (u : Lp ℂ 2 (mu x)),
        V x (mulRep (mu x) g u) = pi g (V x u)) ∧
      (∀ x : S, ∃ (Z : Type u) (_ : MeasurableSpace Z) (_ : StandardBorelSpace Z)
        (_ : MeasurableSingletonClass Z) (Phi : Y → Z) (hPhi : Measurable Phi),
        ∃ _ : IsProbabilityMeasure (Measure.map Phi (mu x)),
          RealizesStandardType (Measure.map Phi (mu x)) ∧
          ∃ U : Lp ℂ 2 (Measure.map Phi (mu x)) ≃ₗᵢ[ℂ] Lp ℂ 2 (mu x),
            ∀ (g : Z → ℂ) (hg : MemLp g ⊤ (Measure.map Phi (mu x)))
              (v : Lp ℂ 2 (Measure.map Phi (mu x))),
              U (multOp g hg v)
                = multOp (fun y => g (Phi y)) (hg.comp_measurePreserving ⟨hPhi, rfl⟩) (U v)) := by

  obtain ⟨S, hS, htop⟩ := exists_rep_cyclic_decomposition pi
  refine ⟨S, fun x => repMeasure pi (x : H), fun x => repEmbedding pi (x : H),
    countable_orthogonalRepCyclicFamily hS,
    fun x => isProbabilityMeasure_repMeasure pi (x : H) (hS.1 (x : H) x.2), ?_,
    fun x g u => repEmbedding_intertwines pi (x : H) g u, ?_⟩
  · refine IsHilbertSum.mk (orthogonalFamily_repEmbedding hS) ?_
    have hrange : (⨆ x : S, LinearMap.range (repEmbedding pi (x : H)).toLinearMap)
        = ⨆ x ∈ S, repCyclicSubspace pi x := by
      rw [iSup_subtype]
      exact iSup_congr fun x => iSup_congr fun _ => range_repEmbedding pi x
    rw [hrange, htop]
  · intro x
    haveI := isProbabilityMeasure_repMeasure pi (x : H) (hS.1 (x : H) x.2)
    haveI : SeparableSpace (Lp ℂ 2 (repMeasure pi (x : H))) :=
      separableSpace_of_linearIsometry (repEmbedding pi (x : H))
    exact separable_Lp_realizes_standard_type (repMeasure pi (x : H))
