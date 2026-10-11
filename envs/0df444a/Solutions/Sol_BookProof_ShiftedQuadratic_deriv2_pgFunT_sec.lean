-- Prove2me | solution 1 for BookProof.ShiftedQuadratic.deriv2_pgFunT_sec
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:41:20.682537+00:00
-- url     : https://prove2.me/submissions/54d7586b-d8f7-48be-8b16-d485de67c1a0

-- Generated from ChapterShiftedQuadraticEsa.lean — solution of BookProof.ShiftedQuadratic.deriv2_pgFunT_sec
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Theorems.Thm_BookProof_ShiftedQuadratic_deriv_pgFunT_sec_at
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_sec_self
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
    deriv (fun t : ℝ => deriv (fun s : ℝ => pgFunT a k p (sec i x s)) t) (x i)
      = pgFunT a k (dPolyT k i (dPolyT k i p)) x := by

  have hfun : (fun t : ℝ => deriv (fun s : ℝ => pgFunT a k p (sec i x s)) t)
      = fun t : ℝ => pgFunT a k (dPolyT k i p) (sec i x t) :=
    funext fun t => deriv_pgFunT_sec_at a k i p x t
  rw [hfun, deriv_pgFunT_sec_at a k i (dPolyT k i p) x (x i), sec_self]
