-- Prove2me | solution 1 for BookProof.QuantumGravityBrstCharge.affBRST_nilpotent
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:39:07.265931+00:00
-- url     : https://prove2.me/submissions/954a6ee0-4e31-4374-99f4-2f5baa956899
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterQuantumGravityBrstCharge.lean — solution of BookProof.QuantumGravityBrstCharge.affBRST_nilpotent
import Mathlib
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_qgBRST_nilpotent
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_affF_jacobi
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_affMat_close
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_affF_antisymm
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
theorem solution : qgBRST affMat affF * qgBRST affMat affF = 0 := qgBRST_nilpotent affMat affF affMat_close affF_antisymm affF_jacobi
