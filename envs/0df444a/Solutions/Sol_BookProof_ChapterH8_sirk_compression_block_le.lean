-- Prove2me | solution 1 for BookProof.ChapterH8.sirk_compression_block_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T04:04:30.88714+00:00
-- url     : https://prove2.me/submissions/8fdf4922-d3a3-498b-bf5b-b100dacd5760

import Mathlib
import Definitions.Def_ChapterH8

set_option autoImplicit false

noncomputable section

open BookProof.ChapterH8 BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6 in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {m n : ℕ} (hmn : m ≤ n) (X : E →L[ℂ] E)
    (Vm : EuclideanSpace ℂ (Fin m) →L[ℂ] E)
    (Vn : EuclideanSpace ℂ (Fin n) →L[ℂ] E)
    (hnest : ∀ i : Fin m, Vm (EuclideanSpace.single i (1 : ℂ))
      = Vn (EuclideanSpace.single (Fin.castLE hmn i) (1 : ℂ)))
    (i j : Fin m) :
    reduceGenerator m Vm X i j
      = reduceGenerator n Vn X (Fin.castLE hmn i) (Fin.castLE hmn j) := by
  simp only [reduceGenerator, Matrix.of_apply, hnest]

end
