-- Prove2me | solution 1 for BookProof.QuantumGravityBrstCharge.ghostOp_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:46:25.418297+00:00
-- url     : https://prove2.me/submissions/86319627-6b04-4076-9b48-9ee91b8b9c8d

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.ghostOp_one
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterQuantumGravity3DGauge
import Mathlib
import Definitions.Def_ChapterQuantumGravityBrstCharge
open BookProof.QuantumGravityBrstCharge



open MvPolynomial BookProof.BRSTNilpotent BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {f : Fin n → Fin n → Fin n → ℝ} {G χ β : Fin n → R}
variable {d : ℕ}
variable {α : Type*}
open BookProof.QuantumGravityBrstCharge

theorem solution: ghostOp 1 = 1 := by
  unfold ghostOp
  exact LinearMap.lTensor_id _ _
