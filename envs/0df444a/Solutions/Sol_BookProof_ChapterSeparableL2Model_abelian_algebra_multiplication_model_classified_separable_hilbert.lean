-- Prove2me | solution 1 for BookProof.ChapterSeparableL2Model.abelian_algebra_multiplication_model_classified_separable_hilbert
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-06T12:09:49.467298+00:00
-- url     : https://prove2.me/submissions/5413506a-0dcf-4f8a-b25a-fbf5c035c889
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSeparableL2Model.lean — solution of BookProof.ChapterSeparableL2Model.abelian_algebra_multiplication_model_classified_separable_hilbert
import Mathlib
import Definitions.Def_ChapterSeparableL2Model
import Theorems.Thm_BookProof_ChapterSeparableL2Model_abelian_multiplication_model_classified_separable_hilbert
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterAbelianCyclicModel
import Definitions.Def_ChapterAbelianDirectSum
import Definitions.Def_ChapterStandardBorelClassification
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterSeparableL2Model



universe u v

noncomputable section

open MeasureTheory TopologicalSpace Complex WeakDual


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
variable {A : Type v} [CommCStarAlgebra A]

set_option maxHeartbeats 1000000 in
theorem solution
    [TopologicalSpace.SeparableSpace H] (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    ∃ (S : Set H) (mu : S → Measure (characterSpace ℂ A))
      (V : ∀ x : S, Lp ℂ 2 (mu x) →ₗᵢ[ℂ] H),
      S.Countable ∧
      (∀ x : S, IsProbabilityMeasure (mu x)) ∧
      IsHilbertSum ℂ (fun x : S => Lp ℂ 2 (mu x)) V ∧
      (∀ (x : S) (a : A) (u : Lp ℂ 2 (mu x)),
        V x (mulRep (mu x) (gelfandModel A a) u) = rho a (V x u)) ∧
      (∀ x : S, ∃ (Z : Type v) (_ : MeasurableSpace Z) (_ : StandardBorelSpace Z)
        (_ : MeasurableSingletonClass Z) (Phi : characterSpace ℂ A → Z)
        (hPhi : Measurable Phi),
        ∃ _ : IsProbabilityMeasure (Measure.map Phi (mu x)),
          RealizesStandardType (Measure.map Phi (mu x)) ∧
          ∃ U : Lp ℂ 2 (Measure.map Phi (mu x)) ≃ₗᵢ[ℂ] Lp ℂ 2 (mu x),
            ∀ (g : Z → ℂ) (hg : MemLp g ⊤ (Measure.map Phi (mu x)))
              (v : Lp ℂ 2 (Measure.map Phi (mu x))),
              U (multOp g hg v)
                = multOp (fun y => g (Phi y)) (hg.comp_measurePreserving ⟨hPhi, rfl⟩) (U v)) := by

  obtain ⟨S, mu, V, hcount, hprob, hsum, hint, hclass⟩ :=
    abelian_multiplication_model_classified_separable_hilbert (gelfandRep rho)
  refine ⟨S, mu, V, hcount, hprob, hsum, fun x a u => ?_, hclass⟩
  rw [hint x (gelfandModel A a) u, gelfandRep_gelfandModel]
