-- Prove2me | solution 1 for BookProof.SmCar.fermiEnergy_quadForm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:35:08.533094+00:00
-- url     : https://prove2.me/submissions/1ee26754-a3ae-45d7-aca4-845b73410895

-- Generated from ChapterSmCarAlgebra.lean — solution of BookProof.SmCar.fermiEnergy_quadForm
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Theorems.Thm_BookProof_SmCar_inner_eq_sum
import Theorems.Thm_BookProof_SmCar_fermiEnergy_apply
open BookProof.SmCar




open Finset

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (m : Fin n → ℝ) (ψ : FermiFock n) :
    (inner ℂ ψ (fermiEnergy m ψ) : ℂ)
      = ∑ S : Finset (Fin n), ((∑ i ∈ S, m i : ℝ) : ℂ) * ((‖ψ S‖ ^ 2 : ℝ) : ℂ) := by

  rw [inner_eq_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [fermiEnergy_apply]
  rw [show (starRingEnd ℂ) (ψ S) * (((∑ i ∈ S, m i : ℝ) : ℂ) * ψ S)
      = ((∑ i ∈ S, m i : ℝ) : ℂ) * ((starRingEnd ℂ) (ψ S) * ψ S) by ring]
  congr 1
  rw [← Complex.normSq_eq_conj_mul_self]
  simp [Complex.normSq_eq_norm_sq]
