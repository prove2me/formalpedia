-- Prove2me | solution 1 for BookProof.SmCar.fermiEnergy_occ
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:35:06.803877+00:00
-- url     : https://prove2.me/submissions/28134731-35ee-4975-8c73-94e9a8fee4f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSmCarAlgebra.lean — solution of BookProof.SmCar.fermiEnergy_occ
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Theorems.Thm_BookProof_SmCar_fermiEnergy_apply
open BookProof.SmCar




open Finset

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (m : Fin n → ℝ) (S : Finset (Fin n)) :
    fermiEnergy m (occ S) = ((∑ i ∈ S, m i : ℝ) : ℂ) • occ S := by

  ext T
  rw [fermiEnergy_apply]
  by_cases h : T = S
  · subst h; simp [occ]
  · simp [occ, EuclideanSpace.single_apply, h]
