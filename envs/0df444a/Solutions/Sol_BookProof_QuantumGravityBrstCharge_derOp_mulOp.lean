-- Prove2me | solution 1 for BookProof.QuantumGravityBrstCharge.derOp_mulOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:03:43.219599+00:00
-- url     : https://prove2.me/submissions/fc238cfc-4877-476a-9485-04c5266343f8

-- Generated from ChapterQuantumGravityBrstCharge.lean — solution of BookProof.QuantumGravityBrstCharge.derOp_mulOp
import Mathlib
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterYangMillsHermite
import Theorems.Thm_BookProof_YangMillsHermite_derOp_apply
open BookProof.QuantumGravityBrstCharge




open MvPolynomial BookProof.BRSTNilpotent BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge
open BookProof.YangMillsHermite

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {f : Fin n → Fin n → Fin n → ℝ} {G χ β : Fin n → R}
variable {d : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution (k l : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    derOp k (X l * p) = X l * derOp k p + (if k = l then p else 0) := by
  classical
  simp only [derOp_apply, Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply,
    smul_eq_C_mul]
  by_cases h : k = l
  · subst h; simp; ring
  · simp [h, Ne.symm h]; ring
