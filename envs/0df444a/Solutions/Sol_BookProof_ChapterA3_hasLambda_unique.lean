-- Prove2me | solution 1 for BookProof.ChapterA3.hasLambda_unique
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:05:17.060808+00:00
-- url     : https://prove2.me/submissions/95a6834f-e50d-4944-b672-2ea07987729d

import Mathlib
import Definitions.Def_ChapterA3c
open BookProof.ChapterA3 Matrix

theorem solution {S Λ Λ' : Matrix (Fin 4) (Fin 4) ℝ}
    (h : HasLambda S Λ) (h' : HasLambda S Λ') : Λ = Λ' := by
  ext μ ν
  have he := (h μ).symm.trans (h' μ)
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 0) he
  have h01 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) he
  have h02 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 2) he
  have h20 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 2 0) he
  simp [Fin.sum_univ_four, mgammaR, mgammaZ, RingHom.mapMatrix_apply,
    Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply] at h00 h01 h02 h20
  fin_cases ν
  · change Λ μ 0 = Λ' μ 0
    linarith
  · exact h00
  · change Λ μ 2 = Λ' μ 2
    linarith
  · exact h01

#print axioms solution
