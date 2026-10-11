-- Prove2me | solution 1 for BookProof.WeakSecondDeriv.IsTestFun.hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:28:54.749072+00:00
-- url     : https://prove2.me/submissions/ccda0886-6f62-439d-ac7f-425f29575003

-- Generated from ChapterWeakSecondDerivative.lean — solution of BookProof.WeakSecondDeriv.IsTestFun.hasCompactSupport
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
open BookProof.WeakSecondDeriv
open BookProof.WeakSecondDeriv.IsTestFun




open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {g : ℝ → ℝ} (h : IsTestFun g) : HasCompactSupport g := h.2
