-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.linIndep_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:56:09.118721+00:00
-- url     : https://prove2.me/submissions/7fc498cb-bf88-40eb-9f30-a32e2e02e0fb

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.linIndep_of_gram
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} (v : Fin n → Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∀ i j, ((v i)ᵀ * v j).trace = if i = j then (4 : ℝ) else 0) :
    LinearIndependent ℝ v := by

  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h_trace : ((∑ j, g j • v j)ᵀ * v i).trace = ∑ j, g j * ((v j)ᵀ * v i).trace := by
    simp [Matrix.transpose_sum, Matrix.sum_mul, Matrix.trace_sum, Matrix.trace_smul]
  simp_all
