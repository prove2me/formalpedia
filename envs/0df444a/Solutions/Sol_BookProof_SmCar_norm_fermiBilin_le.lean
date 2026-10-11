-- Prove2me | solution 1 for BookProof.SmCar.norm_fermiBilin_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:56:26.762951+00:00
-- url     : https://prove2.me/submissions/331f43fc-e269-4b9e-9b53-2204e2faaf60
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSmCarAlgebra.lean — solution of BookProof.SmCar.norm_fermiBilin_le
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Theorems.Thm_BookProof_SmCar_norm_annih_le
import Theorems.Thm_BookProof_SmCar_norm_creat_le
import Theorems.Thm_BookProof_SmCar_fermiBilin_apply
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.SmCar




open Finset

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (h : Matrix (Fin n) (Fin n) ℂ) (ψ : FermiFock n) :
    ‖fermiBilin h ψ‖ ≤ (∑ i : Fin n, ∑ j : Fin n, ‖h i j‖) * ‖ψ‖ := by

  rw [fermiBilin_apply]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [norm_smul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact le_trans (norm_creat_le i _) (norm_annih_le j ψ)
