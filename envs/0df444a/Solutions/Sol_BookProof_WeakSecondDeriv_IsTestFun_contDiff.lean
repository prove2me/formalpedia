-- Prove2me | solution 1 for BookProof.WeakSecondDeriv.IsTestFun.contDiff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:28:53.829651+00:00
-- url     : https://prove2.me/submissions/5113e4a1-7071-42d3-8177-1f3974815974

-- Generated from ChapterWeakSecondDerivative.lean — solution of BookProof.WeakSecondDeriv.IsTestFun.contDiff
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
open BookProof.WeakSecondDeriv
open BookProof.WeakSecondDeriv.IsTestFun




open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {g : ℝ → ℝ} (h : IsTestFun g) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := h.1
