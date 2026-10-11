-- Prove2me | solution 1 for BookProof.WeakSecondDeriv.IsTestFun.integrable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:37:39.814584+00:00
-- url     : https://prove2.me/submissions/f0bc7a93-72d3-479f-a28b-8a66a8d3d02c

-- Generated from ChapterWeakSecondDerivative.lean — solution of BookProof.WeakSecondDeriv.IsTestFun.integrable
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_hasCompactSupport
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_continuous
open BookProof.WeakSecondDeriv
open BookProof.WeakSecondDeriv.IsTestFun




open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {g : ℝ → ℝ} (h : IsTestFun g) : Integrable g volume := h.continuous.integrable_of_hasCompactSupport h.hasCompactSupport
