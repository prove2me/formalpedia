-- Prove2me | solution 1 for BookProof.ChapterG.BRST_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:18:59.801984+00:00
-- url     : https://prove2.me/submissions/33d9ce53-ddd3-4074-8da2-43cc1a306772

-- Generated from ChapterG.lean — solution of BookProof.ChapterG.BRST_nilpotent
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
theorem solution (Q : A) : BRST Q * BRST Q = (0 : Matrix (Fin 2) (Fin 2) A) := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [BRST, Matrix.mul_apply, Fin.sum_univ_two]
