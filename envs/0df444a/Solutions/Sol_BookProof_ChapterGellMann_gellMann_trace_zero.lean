-- Prove2me | solution 1 for BookProof.ChapterGellMann.gellMann_trace_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:45:06.508726+00:00
-- url     : https://prove2.me/submissions/58249a42-2ab1-4e3f-a427-cd78c0f78c3f

-- Generated from ChapterGellMann.lean — solution of BookProof.ChapterGellMann.gellMann_trace_zero
import Mathlib
import Definitions.Def_ChapterGellMann
open BookProof.ChapterGellMann



open Matrix


open BookProof.ChapterParity

set_option maxHeartbeats 1000000 in
theorem solution (a : Fin 8) : (gellMann a).trace = 0 := by

  fin_cases a <;>
    simp [gellMann, Matrix.trace, Matrix.diag, Fin.sum_univ_three, Matrix.smul_apply] ;
    ring
