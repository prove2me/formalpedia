-- Prove2me | solution 1 for BookProof.QuantumGravityBrstCharge.affMat_non_abelian
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:38:47.352017+00:00
-- url     : https://prove2.me/submissions/82a3aa2e-7d14-4d20-be47-41669558d082

-- Generated from ChapterQuantumGravityBrstCharge.lean — solution of BookProof.QuantumGravityBrstCharge.affMat_non_abelian
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
theorem solution : affMat 0 * affMat 1 ≠ affMat 1 * affMat 0 := by

  intro hcon
  have h : (affMat 0 * affMat 1) 0 1 = (affMat 1 * affMat 0) 0 1 := by rw [hcon]
  simp [affMat, show (1 : Fin 84) ≠ 0 by decide] at h
