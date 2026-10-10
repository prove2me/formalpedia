-- Prove2me | solution 1 for BookProof.ChapterH7.reduceGenerator_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:37:44.069977+00:00
-- url     : https://prove2.me/submissions/e1f70f47-1316-4e4f-b026-bda2bf20f8bb

-- Generated from ChapterH7.lean — solution of BookProof.ChapterH7.reduceGenerator_isHermitian
import Mathlib
import Definitions.Def_ChapterH7
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH6
open BookProof.ChapterH7



noncomputable section

open BookProof.ChapterH4 BookProof.ChapterH6
open BookProof.ChapterH6

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (m : ℕ) (V : EuclideanSpace ℂ (Fin m) →L[ℂ] E)
    (X : E →L[ℂ] E) (hX : IsSelfAdjoint X) :
    (reduceGenerator m V X).IsHermitian := by

  have hadj : ContinuousLinearMap.adjoint X = X :=
    (ContinuousLinearMap.star_eq_adjoint X).symm.trans hX
  ext i j
  have h1 : (inner ℂ (X (V (EuclideanSpace.single i (1 : ℂ))))
        (V (EuclideanSpace.single j (1 : ℂ))) : ℂ)
      = inner ℂ (V (EuclideanSpace.single i (1 : ℂ)))
          (X (V (EuclideanSpace.single j (1 : ℂ)))) := by
    conv_lhs => rw [← hadj]
    exact ContinuousLinearMap.adjoint_inner_left X _ _
  simp only [Matrix.conjTranspose_apply, reduceGenerator, Matrix.of_apply, RCLike.star_def]
  rw [inner_conj_symm]
  exact h1
