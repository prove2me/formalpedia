-- Prove2me | solution 1 for BookProof.ShiftedQuadratic.pgFunT_apply_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:41:22.967067+00:00
-- url     : https://prove2.me/submissions/85cfd233-8219-4980-8967-0cf6d4e335db

-- Generated from ChapterShiftedQuadraticEsa.lean — solution of BookProof.ShiftedQuadratic.pgFunT_apply_sum
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Theorems.Thm_BookProof_ShiftedQuadratic_pgFunT_apply_zero
import Theorems.Thm_BookProof_ShiftedHermiteCore_pgFunT_apply_add
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
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
theorem solution {ι : Type*} (a k : Vd d) (s : Finset ι)
    (f : ι → MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFunT a k (∑ v ∈ s, f v) x = ∑ v ∈ s, pgFunT a k (f v) x := by

  classical
  induction s using Finset.induction with
  | empty => simp [pgFunT_apply_zero]
  | insert v s hv ih => rw [Finset.sum_insert hv, Finset.sum_insert hv, pgFunT_apply_add, ih]
