-- Prove2me | solution 1 for BookProof.QuantumGravityBrstCharge.affMat_close
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:39:06.038173+00:00
-- url     : https://prove2.me/submissions/893777ce-3867-4f6f-b611-37a7a7136bdc

-- Generated from ChapterQuantumGravityBrstCharge.lean — solution of BookProof.QuantumGravityBrstCharge.affMat_close
import Mathlib
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravityBrstCharge




open MvPolynomial BookProof.BRSTNilpotent BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {f : Fin n → Fin n → Fin n → ℝ} {G χ β : Fin n → R}
variable {d : ℕ}
variable {α : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (a b : Fin 19) :
    affMat a * affMat b - affMat b * affMat a = ∑ e, affF a b e • affMat e := by

  have hrhs : (∑ e, affF a b e • affMat e) = affEps a b • affMat 1 := by
    simp [affF]
  rw [hrhs]
  by_cases ha0 : a = 0 <;> by_cases ha1 : a = 1 <;> by_cases hb0 : b = 0 <;>
    by_cases hb1 : b = 1 <;>
    simp_all [affMat, affEps, Matrix.single_mul_single_of_ne, show (1 : Fin 84) ≠ 0 by decide]
