-- Prove2me | solution 1 for BookProof.WeakSecondDeriv.IsTestFun.deriv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:29:11.3077+00:00
-- url     : https://prove2.me/submissions/ee7e59ba-50ea-4b55-9f20-e8e280bc0888

-- Generated from ChapterWeakSecondDerivative.lean — solution of BookProof.WeakSecondDeriv.IsTestFun.deriv
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_contDiff
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_hasCompactSupport
open BookProof.WeakSecondDeriv
open BookProof.WeakSecondDeriv.IsTestFun




open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {g : ℝ → ℝ} (h : IsTestFun g) : IsTestFun (_root_.deriv g) := ⟨(contDiff_infty_iff_deriv.1 h.contDiff).2, h.hasCompactSupport.deriv⟩
