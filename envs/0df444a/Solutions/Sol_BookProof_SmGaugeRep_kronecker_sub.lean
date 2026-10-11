-- Prove2me | solution 1 for BookProof.SmGaugeRep.kronecker_sub
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:19:04.988982+00:00
-- url     : https://prove2.me/submissions/33ebae9d-8436-4664-b999-10d4774c5600

-- Generated from ChapterSmGaugeRepresentation.lean — solution of BookProof.SmGaugeRep.kronecker_sub
import Mathlib
import Definitions.Def_ChapterSmGaugeRepresentation
import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterSmBrstGhost
open BookProof.SmGaugeRep




open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.SmBrstGhost

noncomputable section

variable {S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ} {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (C : Matrix (Fin 3) (Fin 3) ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    C ⊗ₖ (A - B) = C ⊗ₖ A - C ⊗ₖ B := by

  ext i j; simp [Matrix.kroneckerMap_apply, mul_sub]
