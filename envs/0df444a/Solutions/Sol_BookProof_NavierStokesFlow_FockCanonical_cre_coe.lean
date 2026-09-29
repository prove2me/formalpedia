-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockCanonical.cre_coe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T20:27:22.228475+00:00
-- url     : https://prove2.me/submissions/429f5c80-3415-49ce-acfd-ffd04706cfc5

import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.FockManyMode BookProof.NavierStokesFlow.HermiteCanonical

variable {d : ℕ} {κ : Fin d → ℝ}

theorem solution
    (i : Fin d) (x : lpFiniteModes (Occ d)) (α : Occ d) :
    (((cre i x : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α =
      (Real.sqrt (α i : ℝ) : ℂ) * ((x : L2I (Occ d)) : Occ d → ℂ) (dn i α) := by
  rfl
