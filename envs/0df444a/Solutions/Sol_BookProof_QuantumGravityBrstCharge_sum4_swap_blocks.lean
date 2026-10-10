-- Prove2me | solution 1 for BookProof.QuantumGravityBrstCharge.sum4_swap_blocks
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:42:53.259817+00:00
-- url     : https://prove2.me/submissions/38b2831f-a6b0-4c06-9091-ed0081b7408c

-- Generated from ChapterQuantumGravityBrstCharge.lean — solution of BookProof.QuantumGravityBrstCharge.sum4_swap_blocks
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
theorem solution [AddCommMonoid α] (F : Fin d → Fin d → Fin d → Fin d → α) :
    ∑ l, ∑ m, ∑ j, ∑ k, F l m j k = ∑ j, ∑ k, ∑ l, ∑ m, F l m j k := by

  calc ∑ l, ∑ m, ∑ j, ∑ k, F l m j k
      = ∑ l, ∑ j, ∑ m, ∑ k, F l m j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ m, ∑ k, F l m j k := Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ k, ∑ m, F l m j k :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ l, ∑ m, F l m j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
