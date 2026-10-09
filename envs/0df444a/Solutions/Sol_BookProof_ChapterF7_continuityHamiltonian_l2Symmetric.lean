-- Prove2me | solution 1 for BookProof.ChapterF7.continuityHamiltonian_l2Symmetric
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:09:03.046998+00:00
-- url     : https://prove2.me/submissions/32ecf311-46cd-4eb5-b653-c9fd81194db9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterF7.lean — solution of BookProof.ChapterF7.continuityHamiltonian_l2Symmetric
import Mathlib
import Definitions.Def_ChapterF7
import Theorems.Thm_BookProof_ChapterF7_mulOp_l2Symmetric
import Theorems.Thm_BookProof_ChapterF7_momentum_l2Symmetric
import Theorems.Thm_BookProof_ChapterF7_anticomm_l2Symmetric
import Theorems.Thm_BookProof_ChapterF7_smul_l2Symmetric
open BookProof.ChapterF7



open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (v : ℝ → ℝ)
    (hv : Function.HasTemperateGrowth (fun x => (v x : ℂ))) :
    IsL2Symmetric
      (((1 : ℂ) / 2) • (momentum.comp (mulOp v hv) + (mulOp v hv).comp momentum)) := by

  refine smul_l2Symmetric (by simp only [map_div₀, map_one, map_ofNat])
    (anticomm_l2Symmetric momentum_l2Symmetric (mulOp_l2Symmetric v hv))
