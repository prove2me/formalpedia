-- Prove2me | solution 1 for BookProof.SmBrstGhost.sum_delta_right
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:49:00.594515+00:00
-- url     : https://prove2.me/submissions/faf19ff1-629b-40b0-9415-aad15fd07062

-- Generated from ChapterSmBrstGhost.lean — solution of BookProof.SmBrstGhost.sum_delta_right
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Theorems.Thm_BookProof_SmBrstGhost_fermiBilin_eq4
open BookProof.SmBrstGhost




open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}
variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {N : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (M P : Matrix (Fin N) (Fin N) ℂ) :
    ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
        (M i j * P k l) • (if l = i then (creat k * annih j : Module.End ℂ (FermiFock N)) else 0)
      = fermiBilin (P * M) := by

  have step1 : ∀ i j k : Fin N,
      (∑ l : Fin N,
        (M i j * P k l) • (if l = i then (creat k * annih j : Module.End ℂ (FermiFock N)) else 0))
        = (M i j * P k i) • (creat k * annih j : Module.End ℂ (FermiFock N)) := by
    intro i j k
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]
    · intro l _ hl
      rw [if_neg hl, smul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  calc ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
        (M i j * P k l) • (if l = i then (creat k * annih j : Module.End ℂ (FermiFock N)) else 0)
      = ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
          (M i j * P k i) • (creat k * annih j : Module.End ℂ (FermiFock N)) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => step1 i j k
    _ = ∑ i : Fin N, ∑ k : Fin N, ∑ j : Fin N,
          (M i j * P k i) • (creat k * annih j : Module.End ℂ (FermiFock N)) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k : Fin N, ∑ i : Fin N, ∑ j : Fin N,
          (M i j * P k i) • (creat k * annih j : Module.End ℂ (FermiFock N)) := Finset.sum_comm
    _ = ∑ k : Fin N, ∑ j : Fin N, ∑ i : Fin N,
          (M i j * P k i) • (creat k * annih j : Module.End ℂ (FermiFock N)) := by
        exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k : Fin N, ∑ j : Fin N,
          ((P * M) k j) • (creat k * annih j : Module.End ℂ (FermiFock N)) := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_smul, Matrix.mul_apply]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = fermiBilin (P * M) := (fermiBilin_eq4 (P * M)).symm
