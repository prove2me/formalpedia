-- Prove2me | solution 1 for BookProof.SmGaugeRep.sum_kronecker_left
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:19:05.884633+00:00
-- url     : https://prove2.me/submissions/a84d21a5-64e3-486b-8101-1563b711828a

-- Generated from ChapterSmGaugeRepresentation.lean — solution of BookProof.SmGaugeRep.sum_kronecker_left
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
theorem solution {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin 3) (Fin 3) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ i ∈ s, A i) ⊗ₖ B = ∑ i ∈ s, (A i ⊗ₖ B) := by

  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_kronecker, ih]
