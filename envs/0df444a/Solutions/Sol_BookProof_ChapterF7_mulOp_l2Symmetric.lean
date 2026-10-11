-- Prove2me | solution 1 for BookProof.ChapterF7.mulOp_l2Symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:03:36.451554+00:00
-- url     : https://prove2.me/submissions/f01bc3e9-3ee3-43b4-a412-940590bc3be3

-- Generated from ChapterF7.lean — solution of BookProof.ChapterF7.mulOp_l2Symmetric
import Mathlib
import Definitions.Def_ChapterF7
import Theorems.Thm_BookProof_YangMillsHermite_mulOp_apply
open BookProof.ChapterF7



open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section


@[simp] private theorem mulOp_apply (v : ℝ → ℝ)
    (hv : Function.HasTemperateGrowth (fun x => (v x : ℂ))) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (mulOp v hv f) x = f x * (v x : ℂ) := by
  simp [mulOp, SchwartzMap.bilinLeftCLM_apply]

set_option maxHeartbeats 1000000 in
theorem solution (v : ℝ → ℝ)
    (hv : Function.HasTemperateGrowth (fun x => (v x : ℂ))) :
    IsL2Symmetric (mulOp v hv) := by

  intro f g
  unfold l2pair
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [mulOp_apply, map_mul, Complex.conj_ofReal]
  ring
