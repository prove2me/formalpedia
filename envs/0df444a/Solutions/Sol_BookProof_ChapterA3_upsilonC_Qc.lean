-- Prove2me | solution 1 for BookProof.ChapterA3.upsilonC_Qc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:33:55.721998+00:00
-- url     : https://prove2.me/submissions/f6386160-92c1-4cad-b414-fcca8e97208b

-- Generated from ChapterA3h.lean — solution of BookProof.ChapterA3.upsilonC_Qc
import Mathlib
import Definitions.Def_ChapterA3h
import Theorems.Thm_BookProof_ChapterA3_det_pauli_comb
import Theorems.Thm_BookProof_ChapterA3_upsilon_apply_comb
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T.det = 1) (x : Fin 4 → ℂ) :
    Qc (fun μ => ∑ ν, UpsilonC T μ ν * x ν) = Qc x := by

  rw [ ← det_pauli_comb, ← det_pauli_comb ];
  rw [ ← upsilon_apply_comb ];
  simp [ hT, Matrix.det_mul ]
