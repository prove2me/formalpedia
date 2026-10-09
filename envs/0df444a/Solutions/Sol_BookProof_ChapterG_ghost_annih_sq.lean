-- Prove2me | solution 1 for BookProof.ChapterG.ghost_annih_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:18:33.003589+00:00
-- url     : https://prove2.me/submissions/bfb2a3a5-28c3-4a66-ab82-76aea7a1b870

-- Generated from ChapterG.lean — solution of BookProof.ChapterG.ghost_annih_sq
import Mathlib
import Definitions.Def_ChapterG
open MeasureTheory
open BookProof.ChapterG



open scoped ComplexConjugate InnerProductSpace Matrix

variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]
variable {A : Type*} [Ring A]

set_option maxHeartbeats 1000000 in
theorem solution : ghostAnnih * ghostAnnih = (0 : Matrix (Fin 2) (Fin 2) A) := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ghostAnnih, Matrix.mul_apply, Fin.sum_univ_two]
