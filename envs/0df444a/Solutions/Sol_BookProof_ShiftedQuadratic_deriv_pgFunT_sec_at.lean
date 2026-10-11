-- Prove2me | solution 1 for BookProof.ShiftedQuadratic.deriv_pgFunT_sec_at
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:41:19.673337+00:00
-- url     : https://prove2.me/submissions/7d90d4fa-65f9-4ef0-9c3d-61e295eb7b76

-- Generated from ChapterShiftedQuadraticEsa.lean — solution of BookProof.ShiftedQuadratic.deriv_pgFunT_sec_at
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Theorems.Thm_BookProof_HyperbolicQuadratic_sec_coord
import Theorems.Thm_BookProof_HyperbolicQuadratic_sec_sec
import Theorems.Thm_BookProof_ShiftedHermiteCore_deriv_pgFunT_sec
import Theorems.Thm_BookProof_ShiftedHermiteCore_pgFunT_apply_add
import Theorems.Thm_BookProof_ShiftedHermiteCore_pgFunT_apply_smul
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
theorem solution (a k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d)
    (t : ℝ) : deriv (fun s : ℝ => pgFunT a k p (sec i x s)) t
      = pgFunT a k (dPolyT k i p) (sec i x t) := by

  have h := deriv_pgFunT_sec a k i p (sec i x t)
  rw [sec_coord] at h
  simp only [sec_sec] at h
  rw [h, dPolyT_apply, pgFunT_apply_add, pgFunT_apply_smul]
