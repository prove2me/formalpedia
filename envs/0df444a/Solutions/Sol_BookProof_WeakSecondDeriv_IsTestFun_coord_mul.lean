-- Prove2me | solution 1 for BookProof.WeakSecondDeriv.IsTestFun.coord_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:29:34.172468+00:00
-- url     : https://prove2.me/submissions/f5cfadf3-54a1-4bfb-bf52-5835848adc28

-- Generated from ChapterWeakSecondDerivative.lean — solution of BookProof.WeakSecondDeriv.IsTestFun.coord_mul
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_contDiff
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_hasCompactSupport
open BookProof.WeakSecondDeriv
open BookProof.WeakSecondDeriv.IsTestFun




open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {g : ℝ → ℝ} (h : IsTestFun g) : IsTestFun (fun x => x * g x) := ⟨contDiff_id.mul h.contDiff, h.hasCompactSupport.mul_left⟩
