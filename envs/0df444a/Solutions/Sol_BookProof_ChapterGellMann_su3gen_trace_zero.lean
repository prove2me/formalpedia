-- Prove2me | solution 1 for BookProof.ChapterGellMann.su3gen_trace_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:45:32.903682+00:00
-- url     : https://prove2.me/submissions/f524b301-b10d-4b94-a5d6-a2e51a432c50

-- Generated from ChapterGellMann.lean — solution of BookProof.ChapterGellMann.su3gen_trace_zero
import Mathlib
import Definitions.Def_ChapterGellMann
import Theorems.Thm_BookProof_ChapterGellMann_gellMann_trace_zero
open BookProof.ChapterGellMann



open Matrix


open BookProof.ChapterParity

set_option maxHeartbeats 1000000 in
theorem solution (a : Fin 8) : (su3gen a).trace = 0 := by

  simp [su3gen, Matrix.trace_smul, gellMann_trace_zero a]
