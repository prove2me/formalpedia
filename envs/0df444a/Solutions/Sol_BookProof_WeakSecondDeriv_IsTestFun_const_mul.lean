-- Prove2me | solution 1 for BookProof.WeakSecondDeriv.IsTestFun.const_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:29:28.923714+00:00
-- url     : https://prove2.me/submissions/dacbacbd-d161-4c7a-8d5a-f191fba06499

-- Generated from ChapterWeakSecondDerivative.lean — solution of BookProof.WeakSecondDeriv.IsTestFun.const_mul
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_contDiff
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_hasCompactSupport
open BookProof.WeakSecondDeriv
open BookProof.WeakSecondDeriv.IsTestFun




open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {g : ℝ → ℝ} (h : IsTestFun g) (a : ℝ) : IsTestFun (fun x => a * g x) := ⟨contDiff_const.mul h.contDiff, h.hasCompactSupport.mul_left⟩
