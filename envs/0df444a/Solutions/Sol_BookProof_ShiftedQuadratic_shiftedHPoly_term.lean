-- Prove2me | solution 1 for BookProof.ShiftedQuadratic.shiftedHPoly_term
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:41:08.920203+00:00
-- url     : https://prove2.me/submissions/76a3aef5-cb60-4090-9245-29ba132986a2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterShiftedQuadraticEsa.lean — solution of BookProof.ShiftedQuadratic.shiftedHPoly_term
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Theorems.Thm_BookProof_ShiftedQuadratic_oscTPoly_apply
import Theorems.Thm_BookProof_ShiftedHermiteCore_momTPoly_apply
import Theorems.Thm_BookProof_ShiftedHermiteCore_mulXTPoly_apply
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
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
theorem solution (c b b' : Fin d → ℝ) (i : Fin d) (hc : c i ≠ 0)
    (p : MvPolynomial (Fin d) ℂ) :
    ((c i : ℝ) : ℂ) • oscTPoly (shiftVec c b) (boostVec c b') i p
        + ((b i : ℝ) : ℂ) • mulXTPoly (shiftVec c b) i p
        + ((b' i : ℝ) : ℂ) • momTPoly (boostVec c b') i p
      = ((c i : ℝ) : ℂ) • oscPoly i p
        + (((-(b' i ^ 2) / (4 * c i) - b i ^ 2 / c i : ℝ)) : ℂ) • p := by

  have hcC : ((c i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [oscTPoly_apply, mulXTPoly_apply, momTPoly_apply, shiftVec_apply, boostVec_apply]
  push_cast
  match_scalars <;> field_simp <;> ring
