-- Prove2me | solution 1 for BookProof.WeakSecondDeriv.IsTestFun.differentiable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:29:10.371014+00:00
-- url     : https://prove2.me/submissions/ef4297d1-7a19-4e7e-8bb4-07b8faea214e

-- Generated from ChapterWeakSecondDerivative.lean — solution of BookProof.WeakSecondDeriv.IsTestFun.differentiable
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_contDiff
open BookProof.WeakSecondDeriv
open BookProof.WeakSecondDeriv.IsTestFun




open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {g : ℝ → ℝ} (h : IsTestFun g) : Differentiable ℝ g := (contDiff_infty_iff_deriv.1 h.contDiff).1
