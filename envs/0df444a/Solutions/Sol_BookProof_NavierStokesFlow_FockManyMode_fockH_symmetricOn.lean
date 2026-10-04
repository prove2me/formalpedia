-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockManyMode.fockH_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T02:33:36.516365+00:00
-- url     : https://prove2.me/submissions/7bbeb5ef-0ec4-48c0-943d-5aafb43f7f5d

-- Generated from ChapterNavierStokesFockManyMode.lean — solution of BookProof.NavierStokesFlow.FockManyMode.fockH_symmetricOn
import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
import Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_fockH_apply
import Theorems.Thm_BookProof_NavierStokesFlow_ShiftHamiltonian_ShiftData_shiftH_symmetricOn
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian


variable {d : ℕ} {κ : Fin d → ℝ}

variable {d : ℕ} {κ : Fin d → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hκ : ∀ i, 0 ≤ κ i) :
    SymmetricOn (maxDom (fockSym κ)) (fockH hκ) := by

  intro x y
  rw [fockH_apply, sum_inner]
  have h : ∀ i : Fin d,
      (inner ℂ (ShiftData.shiftH (modeData hκ i) x : L2I (Occ d)) (y : L2I (Occ d)) : ℂ)
        = inner ℂ (x : L2I (Occ d)) (ShiftData.shiftH (modeData hκ i) y : L2I (Occ d)) :=
    fun i => ShiftData.shiftH_symmetricOn (modeData hκ i) x y
  rw [Finset.sum_congr rfl (fun i _ => h i), ← inner_sum, ← fockH_apply]
