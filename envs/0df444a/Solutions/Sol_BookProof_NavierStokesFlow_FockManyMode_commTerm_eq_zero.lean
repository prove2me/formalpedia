-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockManyMode.commTerm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T02:14:27.784182+00:00
-- url     : https://prove2.me/submissions/4dc9004c-09da-49ec-ab2e-f1db77a0535b

-- Generated from ChapterNavierStokesFockManyMode.lean — solution of BookProof.NavierStokesFlow.FockManyMode.commTerm_eq_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian


variable {d : ℕ} {κ : Fin d → ℝ}

variable {d : ℕ} {κ : Fin d → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hκ : ∀ i, 0 ≤ κ i) (i i₀ : Fin d) (β : Occ d)
    (hprod : ((testState κ i₀ : L2I (Occ d)) : Occ d → ℂ) β
      * ((testState κ i₀ : L2I (Occ d)) : Occ d → ℂ) ((modeData hκ i).shift β) = 0) :
    2 * (modeData hκ i).step * ((modeData hκ i).amp β
      * ((starRingEnd ℂ) (((testState κ i₀ : L2I (Occ d)) : Occ d → ℂ) β)
        * ((testState κ i₀ : L2I (Occ d)) : Occ d → ℂ)
          ((modeData hκ i).shift β)).re) = 0 := by

  rcases mul_eq_zero.mp hprod with h | h <;> rw [h] <;> simp
