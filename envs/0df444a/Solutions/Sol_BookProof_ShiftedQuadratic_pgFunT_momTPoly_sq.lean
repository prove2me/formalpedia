-- Prove2me | solution 1 for BookProof.ShiftedQuadratic.pgFunT_momTPoly_sq
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:41:21.612036+00:00
-- url     : https://prove2.me/submissions/fe7c9add-9655-487f-a106-5e74429344c6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterShiftedQuadraticEsa.lean — solution of BookProof.ShiftedQuadratic.pgFunT_momTPoly_sq
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Theorems.Thm_BookProof_ShiftedQuadratic_momTPoly_eq_smul
import Theorems.Thm_BookProof_ShiftedQuadratic_deriv2_pgFunT_sec
import Theorems.Thm_BookProof_ShiftedHermiteCore_pgFunT_apply_smul
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
theorem solution (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFunT a k (momTPoly k i (momTPoly k i p)) x
      = -deriv (fun t : ℝ => deriv (fun s : ℝ => pgFunT a k p (sec i x s)) t) (x i) := by

  have h1 : momTPoly k i (momTPoly k i p) = (-1 : ℂ) • dPolyT k i (dPolyT k i p) := by
    conv_lhs => rw [momTPoly_eq_smul k i (momTPoly k i p)]
    rw [momTPoly_eq_smul k i p, map_smul, smul_smul]
    congr 1
    linear_combination Complex.I_mul_I
  rw [h1, pgFunT_apply_smul, deriv2_pgFunT_sec]
  ring
