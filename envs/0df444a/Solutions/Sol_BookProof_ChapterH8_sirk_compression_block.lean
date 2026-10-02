-- Prove2me | solution 1 for BookProof.ChapterH8.sirk_compression_block
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T04:12:36.385008+00:00
-- url     : https://prove2.me/submissions/ee7f4042-b463-4132-8e3e-6c383a1bb6f3

import Mathlib
import Definitions.Def_ChapterH8

set_option autoImplicit false

noncomputable section

open BookProof.ChapterH8 BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6 in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (n : ℕ) (X : E →L[ℂ] E)
    (Vn : EuclideanSpace ℂ (Fin n) →L[ℂ] E)
    (Vm : EuclideanSpace ℂ (Fin (n + 1)) →L[ℂ] E)
    (hnest : ∀ i : Fin n, Vn (EuclideanSpace.single i (1 : ℂ))
      = Vm (EuclideanSpace.single (Fin.castSucc i) (1 : ℂ)))
    (i j : Fin n) :
    reduceGenerator n Vn X i j
      = reduceGenerator (n + 1) Vm X (Fin.castSucc i) (Fin.castSucc j) := by
  simp only [reduceGenerator, Matrix.of_apply, hnest]

end
