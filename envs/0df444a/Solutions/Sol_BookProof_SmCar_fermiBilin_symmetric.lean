-- Prove2me | solution 1 for BookProof.SmCar.fermiBilin_symmetric
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:56:12.783498+00:00
-- url     : https://prove2.me/submissions/8d286c9b-0580-43c8-b2ab-b5e50fd93143
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSmCarAlgebra.lean — solution of BookProof.SmCar.fermiBilin_symmetric
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Theorems.Thm_BookProof_SmCar_inner_creat_left
import Theorems.Thm_BookProof_SmCar_inner_annih_left
import Theorems.Thm_BookProof_SmCar_fermiBilin_apply
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.SmCar




open Finset

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {h : Matrix (Fin n) (Fin n) ℂ} (hh : h.conjTranspose = h)
    (ψ φ : FermiFock n) :
    (inner ℂ (fermiBilin h ψ) φ : ℂ) = inner ℂ ψ (fermiBilin h φ) := by

  have hentry : ∀ i j, (starRingEnd ℂ) (h j i) = h i j := by
    intro i j
    have := congrFun (congrFun hh i) j
    simpa [Matrix.conjTranspose_apply] using this
  rw [fermiBilin_apply, fermiBilin_apply]
  rw [sum_inner]
  simp only [sum_inner, inner_smul_left, inner_sum, inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [inner_creat_left, inner_annih_left]
  rw [hentry i j]
