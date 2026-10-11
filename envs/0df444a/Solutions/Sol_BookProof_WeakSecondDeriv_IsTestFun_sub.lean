-- Prove2me | solution 1 for BookProof.WeakSecondDeriv.IsTestFun.sub
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:37:40.706549+00:00
-- url     : https://prove2.me/submissions/a22019dd-0034-481c-9b2e-d62bebf5de7f

-- Generated from ChapterWeakSecondDerivative.lean — solution of BookProof.WeakSecondDeriv.IsTestFun.sub
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_contDiff
open BookProof.WeakSecondDeriv
open BookProof.WeakSecondDeriv.IsTestFun




open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {f g : ℝ → ℝ} (h1 : IsTestFun f) (h2 : IsTestFun g) :
    IsTestFun (fun x => f x - g x) := ⟨h1.contDiff.sub h2.contDiff, h1.2.sub h2.2⟩
