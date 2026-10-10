-- Prove2me | solution 1 for BookProof.ChapterPauliLorentz.hermMat_eq_pauli
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:36:43.373917+00:00
-- url     : https://prove2.me/submissions/b5eb8037-df6a-4f71-9457-618845eab303

-- Generated from ChapterPauliLorentz.lean — solution of BookProof.ChapterPauliLorentz.hermMat_eq_pauli
import Mathlib
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliLorentz



open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (x : Fin 4 → ℝ) :
    hermMat x = (x 0 : ℂ) • σ0 + (x 1 : ℂ) • σ1 + (x 2 : ℂ) • σ2 + (x 3 : ℂ) • σ3 := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hermMat, σ0, σ1, σ2, σ3] <;> ring
