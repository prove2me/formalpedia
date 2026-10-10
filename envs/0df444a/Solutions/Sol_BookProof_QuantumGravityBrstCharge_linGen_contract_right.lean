-- Prove2me | solution 1 for BookProof.QuantumGravityBrstCharge.linGen_contract_right
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:42:57.478789+00:00
-- url     : https://prove2.me/submissions/8cd74f69-1e78-42d7-ba71-84ad07b1dcbb

-- Generated from ChapterQuantumGravityBrstCharge.lean — solution of BookProof.QuantumGravityBrstCharge.linGen_contract_right
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
    (∑ j, ∑ k, ∑ l, ∑ m, (A j k * B l m) • (if j = m then elemGen l k else 0))
      = linGen (B * A) := by

  classical
  have step1 : ∀ j k l : Fin d,
      (∑ m, (A j k * B l m) • (if j = m then elemGen (d := d) l k else 0))
        = (A j k * B l j) • elemGen l k := by
    intro j k l
    simp [Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => step1 j k l, linGen_def]
  calc (∑ j, ∑ k, ∑ l, (A j k * B l j) • elemGen (d := d) l k)
      = ∑ j, ∑ l, ∑ k, (A j k * B l j) • elemGen (d := d) l k :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ l, ∑ j, ∑ k, (A j k * B l j) • elemGen (d := d) l k := Finset.sum_comm
    _ = ∑ l, ∑ k, ∑ j, (A j k * B l j) • elemGen (d := d) l k :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ l, ∑ k, ((B * A) l k) • elemGen (d := d) l k := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_smul, Matrix.mul_apply]
        congr 1
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
