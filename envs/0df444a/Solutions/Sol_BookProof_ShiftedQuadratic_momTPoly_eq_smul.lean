-- Prove2me | solution 1 for BookProof.ShiftedQuadratic.momTPoly_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-12T11:20:02.626987+00:00
-- url     : https://prove2.me/submissions/680d0c6f-eba8-4c3b-ba89-b19daebb9127

-- Generated from ChapterShiftedQuadraticEsa.lean — solution of BookProof.ShiftedQuadratic.momTPoly_eq_smul
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Theorems.Thm_BookProof_HyperbolicQuadratic_dPoly_apply
import Theorems.Thm_BookProof_HyperbolicQuadratic_momPoly_apply_prime
import Theorems.Thm_BookProof_ShiftedHermiteCore_momTPoly_apply
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.ShiftedQuadratic




open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.ShiftedHermiteCore
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momTPoly k i p = (-Complex.I) • dPolyT k i p := by

  rw [momTPoly_apply, dPolyT_apply, momPoly_apply_prime i p, ← dPoly_apply]
  match_scalars <;> (ring_nf; all_goals (rw [Complex.I_sq]; ring))
