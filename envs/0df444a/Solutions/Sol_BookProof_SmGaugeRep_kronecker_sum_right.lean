-- Prove2me | solution 1 for BookProof.SmGaugeRep.kronecker_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:19:06.744711+00:00
-- url     : https://prove2.me/submissions/a2784c10-90ed-4089-8748-00518f92e50c

-- Generated from ChapterSmGaugeRepresentation.lean — solution of BookProof.SmGaugeRep.kronecker_sum_right
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
theorem solution {ι : Type*} (s : Finset ι) (A : Matrix (Fin 3) (Fin 3) ℂ)
    (B : ι → Matrix (Fin 2) (Fin 2) ℂ) :
    A ⊗ₖ (∑ i ∈ s, B i) = ∑ i ∈ s, (A ⊗ₖ B i) := by

  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.kronecker_add, ih]
