-- Prove2me | solution 1 for BookProof.QuantumGravityBrstCharge.qgBRST_abelian_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:38:31.596984+00:00
-- url     : https://prove2.me/submissions/5925dd7b-28e1-4167-a658-f062627124d9

-- Generated from ChapterQuantumGravityBrstCharge.lean — solution of BookProof.QuantumGravityBrstCharge.qgBRST_abelian_nilpotent
import Mathlib
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_brst_abelian_nilpotent
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_linGen_zero
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_linGen_bracket
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_bosOp_mul
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_bosOp_sub
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_bosOp_ghostOp_comm
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_qgGhostCar
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterSmBrstGhost
open BookProof.QuantumGravityBrstCharge




open MvPolynomial BookProof.BRSTNilpotent BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {f : Fin n → Fin n → Fin n → ℝ} {G χ β : Fin n → R}
variable {d : ℕ}
variable {α : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (M : Fin 19 → Matrix (Fin 84) (Fin 84) ℝ)
    (hcomm : ∀ a b, M a * M b = M b * M a) :
    glin (qgConstraint M) qgChi * glin (qgConstraint M) qgChi = 0 := by

  refine brst_abelian_nilpotent (β := qgBeta) qgGhostCar (fun a b => bosOp_ghostOp_comm _ _)
    (fun a b => bosOp_ghostOp_comm _ _) fun a b => ?_
  have h : linGen (M a) * linGen (M b) - linGen (M b) * linGen (M a) = 0 := by
    rw [linGen_bracket, hcomm a b, sub_self, linGen_zero]
  have h0 : bosOp (linGen (M a)) * bosOp (linGen (M b))
      - bosOp (linGen (M b)) * bosOp (linGen (M a)) = 0 := by
    rw [← bosOp_mul, ← bosOp_mul, ← bosOp_sub, h, bosOp]
    simp
  exact sub_eq_zero.mp h0
