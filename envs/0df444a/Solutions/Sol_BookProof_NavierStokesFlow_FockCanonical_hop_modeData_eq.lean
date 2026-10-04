-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockCanonical.hop_modeData_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T02:34:43.832148+00:00
-- url     : https://prove2.me/submissions/05942ae0-b86d-4954-91bf-1569c0fe69b2

-- Generated from ChapterNavierStokesFockCanonical.lean — solution of BookProof.NavierStokesFlow.FockCanonical.hop_modeData_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_modeShift_dn_dn
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical

variable {d : ℕ} {κ : Fin d → ℝ}

variable {d : ℕ} {κ : Fin d → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hκ : ∀ i, 0 ≤ κ i) (i : Fin d) (g : Occ d → ℂ) (β : Occ d) :
    (modeData hκ i).hop g β = if 2 ≤ β i then g (dn i (dn i β)) else 0 := by

  by_cases h : 2 ≤ β i
  · rw [if_pos h]
    have hβ : modeShift i (dn i (dn i β)) = β := modeShift_dn_dn i h
    conv_lhs => rw [← hβ]
    exact ShiftData.hop_shift (modeData hκ i) g _
  · rw [if_neg h]
    refine ShiftData.hop_eq_zero (modeData hκ i) g ?_
    rintro ⟨α, hα⟩
    apply h
    have hs : (modeData hκ i).shift α = modeShift i α := rfl
    rw [hs] at hα
    rw [← hα, modeShift_self]
    omega
