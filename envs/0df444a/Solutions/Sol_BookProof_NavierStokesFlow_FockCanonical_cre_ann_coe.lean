-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockCanonical.cre_ann_coe
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T02:14:31.656852+00:00
-- url     : https://prove2.me/submissions/4fc97392-51f3-4d22-99b0-35b75c65b2c1

-- Generated from ChapterNavierStokesFockCanonical.lean — solution of BookProof.NavierStokesFlow.FockCanonical.cre_ann_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_dn_self
import Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_ann_coe
import Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_cre_coe
import Theorems.Thm_BookProof_FockSecondQuantization_up_dn
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteCanonical_sqrt_mul_sqrt
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical

variable {d : ℕ} {κ : Fin d → ℝ}

variable {d : ℕ} {κ : Fin d → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (x : lpFiniteModes (Occ d)) (α : Occ d) :
    (((cre i (ann i x) : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α
      = (α i : ℂ) * ((x : L2I (Occ d)) : Occ d → ℂ) α := by

  rw [cre_coe]
  rcases Nat.eq_zero_or_pos (α i) with h0 | h1
  · rw [h0]
    simp
  · rw [ann_coe, dn_self, up_dn i h1]
    have hcast : ((α i - 1 : ℕ) : ℝ) + 1 = (α i : ℝ) := by
      have : (1 : ℕ) ≤ α i := h1
      push_cast [Nat.cast_sub this]
      ring
    rw [hcast, ← mul_assoc, sqrt_mul_sqrt _ (by positivity)]
    push_cast
    ring
