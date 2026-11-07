-- Prove2me | solution 1 for BookProof.ChapterH8.krylovOrthonormal_span
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-06T14:03:46.069283+00:00
-- url     : https://prove2.me/submissions/86330495-51b1-496b-badb-081d30000cf0

-- Generated from ChapterH8Bases.lean — solution of BookProof.ChapterH8.krylovOrthonormal_span
import Mathlib
import Definitions.Def_ChapterH8Bases
open BookProof.ChapterH8



noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (H : E →ₗ[ℂ] E) (v : E) (n : ℕ) :
    Submodule.span ℂ (Set.range (fun i : Fin n => krylovOrthonormalSeq H v (i : ℕ)))
      = krylovSpan H v n := by

  -- `Fin n` ranges are the first `n` members of the `ℕ`-indexed sequence, so the
  -- Gram–Schmidt span lemmas (`Iio`, then `Normed`) apply verbatim.
  have hrange : (Set.range (fun i : Fin n => krylovOrthonormalSeq H v (i : ℕ)))
      = krylovOrthonormalSeq H v '' Set.Iio n := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [hrange, krylovOrthonormalSeq, InnerProductSpace.span_gramSchmidtNormed,
    InnerProductSpace.span_gramSchmidt_Iio, krylovSpan]
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
