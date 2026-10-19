-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DiagonalEsa.diagOp_basis
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:24:47.04066+00:00
-- url     : https://prove2.me/submissions/875b0fb1-7954-41aa-957f-56950bf34622

import Mathlib
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesDeficiency.lean — theorem BookProof.NavierStokesFlow.DiagonalEsa.diagOp_basis
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.DiagonalEsa


open scoped ENNReal


theorem solution (c : ℕ → ℝ) (n : ℕ) : diagOp c (basis n) = ((c n : ℂ)) • basis n := by
  apply Subtype.ext
  ext k
  show diagFun c _ k = _
  simp only [diagFun, basis, Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases h : k = n
  · subst h; simp
  · simp [lp.single_apply, Pi.single_apply, h]

