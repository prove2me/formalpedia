-- Prove2me | solution 1 for BookProof.ChapterAbelianDiagonalCountable.diagOp_injective
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:23:32.528611+00:00
-- url     : https://prove2.me/submissions/bf80e292-fd8a-4e1d-bff5-d339f5859e42

-- Generated from ChapterAbelianDiagonalCountable.lean — theorem BookProof.ChapterAbelianDiagonalCountable.diagOp_injective
import Mathlib
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable


open scoped ENNReal

noncomputable section
open BookProof.ChapterAbelianDiagonalCountable

theorem solution: Function.Injective diagOp := by
  intro d e h
  apply lp.ext
  funext i
  have h1 := congrArg (fun T : Ell2C →L[ℂ] Ell2C => ((T (atom i) : Ell2C) : ℕ → ℂ) i) h
  simpa [diagOp, atom, LinearMap.mkContinuous_apply, diagLin_apply, lp.single_apply] using h1
