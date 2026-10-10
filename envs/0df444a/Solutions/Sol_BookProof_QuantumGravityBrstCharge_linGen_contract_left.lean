-- Prove2me | solution 1 for BookProof.QuantumGravityBrstCharge.linGen_contract_left
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:42:55.953445+00:00
-- url     : https://prove2.me/submissions/c7219813-4fd4-4c45-9410-034f5b25cc88

-- Generated from ChapterQuantumGravityBrstCharge.lean — solution of BookProof.QuantumGravityBrstCharge.linGen_contract_left
import Mathlib
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_linGen_def
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
theorem solution (A B : Matrix (Fin d) (Fin d) ℝ) :
    (∑ j, ∑ k, ∑ l, ∑ m, (A j k * B l m) • (if k = l then elemGen j m else 0))
      = linGen (A * B) := by

  classical
  have step1 : ∀ j k : Fin d,
      (∑ l, ∑ m, (A j k * B l m) • (if k = l then elemGen (d := d) j m else 0))
        = ∑ m, (A j k * B k m) • elemGen j m := by
    intro j k
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp [Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => step1 j k, linGen_def]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_smul, Matrix.mul_apply]
