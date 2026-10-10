-- Prove2me | solution 1 for BookProof.QuantizationWeyl.comm_XY
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:42:14.346686+00:00
-- url     : https://prove2.me/submissions/89b14321-c239-41d0-bcf0-bf7c8dec5def

-- Generated from ChapterQuantizationWeyl.lean — solution of BookProof.QuantizationWeyl.comm_XY
import Mathlib
import Definitions.Def_ChapterQuantizationWeyl
open BookProof.QuantizationWeyl



open NormedSpace
open scoped Matrix


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option maxHeartbeats 1000000 in
theorem solution : Xgen * Ygen - Ygen * Xgen = Zgen := by

  unfold Xgen Ygen Zgen; ext i j; fin_cases i <;> fin_cases j <;>
    simp
