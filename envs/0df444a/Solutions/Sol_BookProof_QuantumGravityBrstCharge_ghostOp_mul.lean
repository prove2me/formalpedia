-- Prove2me | solution 1 for BookProof.QuantumGravityBrstCharge.ghostOp_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:43:06.147249+00:00
-- url     : https://prove2.me/submissions/3251f571-9e7c-48d0-8ab0-f5cd7699e685

-- Generated from ChapterQuantumGravityBrstCharge.lean — solution of BookProof.QuantumGravityBrstCharge.ghostOp_mul
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
theorem solution (S T : Module.End ℂ ghostSpace) : ghostOp (S * T) = ghostOp S * ghostOp T := by

  simp [ghostOp, Module.End.mul_eq_comp, LinearMap.lTensor_comp]
