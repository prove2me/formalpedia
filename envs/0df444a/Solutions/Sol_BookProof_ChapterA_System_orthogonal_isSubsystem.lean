-- Prove2me | solution 1 for BookProof.ChapterA.System.orthogonal_isSubsystem
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:36:15.430587+00:00
-- url     : https://prove2.me/submissions/cb539376-03c9-4fc5-9786-ea0b5cbd2fa3

import Mathlib
import Definitions.Def_ChapterA
open BookProof.ChapterA BookProof.ChapterA.System
open scoped ComplexConjugate InnerProductSpace
variable {𝔽 : Type*} [RCLike 𝔽] {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace 𝔽 V] [CompleteSpace V]

theorem solution (M : System 𝔽 V) (hM : IsNormal M)
    {W : Submodule 𝔽 V} (hW : IsSubsystem M W) : IsSubsystem M Wᗮ := by
  refine ⟨W.isClosed_orthogonal, ?_⟩
  intro m hm w hw
  rw [Submodule.mem_orthogonal] at hw ⊢
  intro v hv
  rw [← ContinuousLinearMap.adjoint_inner_left]
  exact hw _ (hW.2 _ (hM m hm) _ hv)

#print axioms solution
