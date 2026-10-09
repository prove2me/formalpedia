-- Prove2me | solution 1 for BookProof.SmBrstGhost.fermiBilin_comm_creat
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:49:01.728264+00:00
-- url     : https://prove2.me/submissions/d5b7ed3d-4578-470a-a1c0-8a6686d878e2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSmBrstGhost.lean — solution of BookProof.SmBrstGhost.fermiBilin_comm_creat
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Theorems.Thm_BookProof_SmBrstGhost_annih_mul_creat
import Theorems.Thm_BookProof_SmBrstGhost_creat_mul_creat
import Theorems.Thm_BookProof_SmBrstGhost_fermiBilin_eq4
open BookProof.SmBrstGhost




open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}
variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {N : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {A : Matrix (Fin N) (Fin N) ℂ} {k : Fin N}
    (hcol : ∀ i, A i k = 0) :
    (fermiBilin A : Module.End ℂ (FermiFock N)) * creat k
      = creat k * fermiBilin A := by

  rw [fermiBilin_eq4, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j = k
  · subst h
    rw [hcol i, zero_smul, zero_mul, mul_zero]
  · rw [smul_mul_assoc, mul_smul_comm]
    congr 1
    have h1 : (annih j : Module.End ℂ (FermiFock N)) * creat k = -(creat k * annih j) := by
      rw [annih_mul_creat j k, if_neg h, zero_sub]
    calc (creat i * annih j : Module.End ℂ (FermiFock N)) * creat k
        = creat i * ((annih j : Module.End ℂ (FermiFock N)) * creat k) := by noncomm_ring
      _ = creat i * -(creat k * annih j) := by rw [h1]
      _ = -((creat i : Module.End ℂ (FermiFock N)) * creat k) * annih j := by noncomm_ring
      _ = -(-((creat k : Module.End ℂ (FermiFock N)) * creat i)) * annih j := by
            rw [creat_mul_creat i k]
      _ = creat k * (creat i * annih j) := by noncomm_ring
