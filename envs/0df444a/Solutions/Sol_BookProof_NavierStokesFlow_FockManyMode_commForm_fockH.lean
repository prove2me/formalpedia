-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockManyMode.commForm_fockH
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T02:32:27.898988+00:00
-- url     : https://prove2.me/submissions/9b47a53c-22b9-43ed-abfd-f2c619e7b1bd

-- Generated from ChapterNavierStokesFockManyMode.lean — solution of BookProof.NavierStokesFlow.FockManyMode.commForm_fockH
import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
import Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_fockH_apply
import Theorems.Thm_BookProof_FarisLavine_commForm_eq
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian


variable {d : ℕ} {κ : Fin d → ℝ}

variable {d : ℕ} {κ : Fin d → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hκ : ∀ i, 0 ≤ κ i) (x : maxDom (fockSym κ)) :
    commForm (fockH hκ) (diagMax (fockSym κ)) x
      = ∑ i, commForm (ShiftData.shiftH (modeData hκ i)) (diagMax (fockSym κ)) x := by

  rw [commForm_eq, fockH_apply, sum_inner]
  rw [show ((∑ i, (inner ℂ (ShiftData.shiftH (modeData hκ i) x : L2I (Occ d))
      (diagMax (fockSym κ) x : L2I (Occ d)) : ℂ)).im)
      = ∑ i, (inner ℂ (ShiftData.shiftH (modeData hκ i) x : L2I (Occ d))
        (diagMax (fockSym κ) x : L2I (Occ d)) : ℂ).im from
    map_sum Complex.imAddGroupHom _ _]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => (commForm_eq _ _ x).symm
