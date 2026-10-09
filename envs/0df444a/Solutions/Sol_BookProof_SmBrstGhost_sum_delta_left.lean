-- Prove2me | solution 1 for BookProof.SmBrstGhost.sum_delta_left
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:48:47.391471+00:00
-- url     : https://prove2.me/submissions/da063f6d-1d44-4dcc-8bfb-7b1b0b3c4093

-- Generated from ChapterSmBrstGhost.lean — solution of BookProof.SmBrstGhost.sum_delta_left
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
        (M i j * P k l) • (if j = k then (creat i * annih l : Module.End ℂ (FermiFock N)) else 0)
      = fermiBilin (M * P) := by

  have step1 : ∀ i j : Fin N,
      (∑ k : Fin N, ∑ l : Fin N,
        (M i j * P k l) • (if j = k then (creat i * annih l : Module.End ℂ (FermiFock N)) else 0))
        = ∑ l : Fin N, (M i j * P j l) • (creat i * annih l : Module.End ℂ (FermiFock N)) := by
    intro i j
    rw [Finset.sum_eq_single j]
    · exact Finset.sum_congr rfl fun l _ => by rw [if_pos rfl]
    · intro k _ hk
      exact Finset.sum_eq_zero fun l _ => by rw [if_neg (Ne.symm hk), smul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  calc ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
        (M i j * P k l) • (if j = k then (creat i * annih l : Module.End ℂ (FermiFock N)) else 0)
      = ∑ i : Fin N, ∑ j : Fin N, ∑ l : Fin N,
          (M i j * P j l) • (creat i * annih l : Module.End ℂ (FermiFock N)) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => step1 i j
    _ = ∑ i : Fin N, ∑ l : Fin N, ∑ j : Fin N,
          (M i j * P j l) • (creat i * annih l : Module.End ℂ (FermiFock N)) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i : Fin N, ∑ l : Fin N,
          ((M * P) i l) • (creat i * annih l : Module.End ℂ (FermiFock N)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
        rw [← Finset.sum_smul, Matrix.mul_apply]
    _ = fermiBilin (M * P) := (fermiBilin_eq4 (M * P)).symm
