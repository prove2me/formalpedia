-- Prove2me | solution 1 for BookProof.QuantumGravityBrstCharge.chi_anticomm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:42:35.267915+00:00
-- url     : https://prove2.me/submissions/ceb4f03a-2546-4edb-88f7-f9b0be20d877

-- Generated from ChapterQuantumGravityBrstCharge.lean — solution of BookProof.QuantumGravityBrstCharge.chi_anticomm
import Mathlib
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterBRSTNilpotent
open BookProof.QuantumGravityBrstCharge




open MvPolynomial BookProof.BRSTNilpotent BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {f : Fin n → Fin n → Fin n → ℝ} {G χ β : Fin n → R}

set_option maxHeartbeats 1000000 in
theorem solution (hCAR : GhostCAR χ β) (a b : Fin n) : χ a * χ b = -(χ b * χ a) := eq_neg_of_add_eq_zero_left (hCAR.chichi a b)
