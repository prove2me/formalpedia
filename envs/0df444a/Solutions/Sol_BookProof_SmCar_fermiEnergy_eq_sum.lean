-- Prove2me | solution 1 for BookProof.SmCar.fermiEnergy_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:35:04.735333+00:00
-- url     : https://prove2.me/submissions/c307c277-39b9-4a51-b47d-eb7bf070692e

-- Generated from ChapterSmCarAlgebra.lean — solution of BookProof.SmCar.fermiEnergy_eq_sum
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Theorems.Thm_BookProof_SmCar_fermiBilin_apply
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.SmCar




open Finset

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (m : Fin n → ℝ) (ψ : FermiFock n) :
    fermiEnergy m ψ = ∑ i : Fin n, (m i : ℂ) • creat i (annih i ψ) := by

  rw [fermiEnergy, fermiBilin_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro b _ hb
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hb), zero_smul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi
