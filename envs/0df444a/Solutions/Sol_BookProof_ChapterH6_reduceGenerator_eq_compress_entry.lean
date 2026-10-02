-- Prove2me | solution 1 for BookProof.ChapterH6.reduceGenerator_eq_compress_entry
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T02:39:28.024219+00:00
-- url     : https://prove2.me/submissions/b743daa0-e0b2-4f5d-bc6b-e16b1ce27a3f

import Mathlib
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH4

set_option autoImplicit false

open BookProof.ChapterH4
open BookProof.ChapterH6

noncomputable section

open Filter Topology

open BookProof.ChapterH4 BookProof.ChapterH6 in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (m : ℕ)
    (V : EuclideanSpace ℂ (Fin m) →L[ℂ] E) (X : E →L[ℂ] E) (i j : Fin m) :
    reduceGenerator m V X i j
      = inner ℂ (EuclideanSpace.single i (1 : ℂ))
          (compress V X (EuclideanSpace.single j (1 : ℂ))) := by
  rw [compress, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  rfl

end

