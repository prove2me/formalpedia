-- Prove2me | solution 1 for BookProof.QuantumGravityBrstCharge.bosOp_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:43:04.805533+00:00
-- url     : https://prove2.me/submissions/ffb35e84-52f4-4f72-9068-5b45dfaad508

-- Generated from ChapterQuantumGravityBrstCharge.lean — solution of BookProof.QuantumGravityBrstCharge.bosOp_sum
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
theorem solution {n : ℕ} (T : Fin n → Module.End ℂ qgPoly) :
    bosOp (∑ e, T e) = ∑ e, bosOp (T e) := map_sum (LinearMap.rTensorHom (R := ℂ) ghostSpace) T Finset.univ
