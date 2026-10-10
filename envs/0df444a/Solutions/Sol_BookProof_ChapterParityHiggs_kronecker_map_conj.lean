-- Prove2me | solution 1 for BookProof.ChapterParityHiggs.kronecker_map_conj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:59.036559+00:00
-- url     : https://prove2.me/submissions/becf9673-dbb7-41c8-9453-004a9292d883

-- Generated from ChapterParityHiggs.lean — solution of BookProof.ChapterParityHiggs.kronecker_map_conj
import Mathlib
import Definitions.Def_ChapterParityHiggs
import Definitions.Def_ChapterParity
open BookProof.ChapterParityHiggs



open Matrix
open scoped Kronecker
open scoped ComplexConjugate


open BookProof.ChapterParity

set_option maxHeartbeats 1000000 in
theorem solution {l m n p : Type*} (A : Matrix l m ℂ) (B : Matrix n p ℂ) :
    (A ⊗ₖ B).map (starRingEnd ℂ)
      = (A.map (starRingEnd ℂ)) ⊗ₖ (B.map (starRingEnd ℂ)) := by

  ext i j
  simp [Matrix.kroneckerMap_apply, Matrix.map_apply, map_mul]
