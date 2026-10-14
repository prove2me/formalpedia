-- Prove2me | solution 1 for BookProof.ShiftedQuadratic.shiftedHPoly_apply_eq_differential
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:41:24.873572+00:00
-- url     : https://prove2.me/submissions/9773685e-48b5-4d23-b49a-b3b91196b5a6

-- Generated from ChapterShiftedQuadraticEsa.lean — solution of BookProof.ShiftedQuadratic.shiftedHPoly_apply_eq_differential
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHPoly_apply
import Theorems.Thm_BookProof_ShiftedQuadratic_pgFunT_momTPoly_sq
import Theorems.Thm_BookProof_ShiftedQuadratic_pgFunT_apply_sum
import Theorems.Thm_BookProof_ShiftedQuadratic_oscTPoly_eq
import Theorems.Thm_BookProof_ShiftedHermiteCore_pgFunT_apply_add
import Theorems.Thm_BookProof_ShiftedHermiteCore_pgFunT_apply_smul
import Theorems.Thm_BookProof_ShiftedHermiteCore_pgFunT_momTPoly
import Theorems.Thm_BookProof_ShiftedHermiteCore_pgFunT_mulXTPoly
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
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
theorem solution (a k : Vd d) (c b b' : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFunT a k (shiftedHPoly a k c b b' p) x
      = ∑ i, (((c i : ℝ) : ℂ)
            * (-deriv (fun t : ℝ => deriv (fun s : ℝ => pgFunT a k p (sec i x s)) t) (x i)
                + (((x i : ℝ) : ℂ) ^ 2 / 4) * pgFunT a k p x)
          + ((b i : ℝ) : ℂ) * (((x i : ℝ) : ℂ) * pgFunT a k p x)
          + ((b' i : ℝ) : ℂ)
              * (-Complex.I * deriv (fun t : ℝ => pgFunT a k p (sec i x t)) (x i))) := by

  rw [shiftedHPoly_apply, pgFunT_apply_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pgFunT_apply_add, pgFunT_apply_add, pgFunT_apply_smul, pgFunT_apply_smul,
    pgFunT_apply_smul, oscTPoly_eq, pgFunT_apply_add, pgFunT_apply_smul,
    pgFunT_momTPoly_sq, pgFunT_mulXTPoly, pgFunT_mulXTPoly, pgFunT_momTPoly]
  ring
