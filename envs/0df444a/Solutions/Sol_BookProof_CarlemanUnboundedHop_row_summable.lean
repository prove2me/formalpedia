-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.row_summable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:01:00.8708+00:00
-- url     : https://prove2.me/submissions/d2c91577-afa0-4de4-9654-7d5226542543

-- Generated from ChapterCarlemanUnboundedHop.lean — solution of BookProof.CarlemanUnboundedHop.row_summable
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop




open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution {a : ℕ → ℕ → ℂ} (hk : IsL2Kernel a) (k : ℕ) :
    Summable fun n : ℕ => ‖a k n‖ ^ 2 := by

  have hcol : Summable fun n : ℕ => ‖a n k‖ ^ 2 := by
    have hsum := (hk.col k).summable (p := 2) (by norm_num)
    refine hsum.congr fun n => ?_
    rw [show ENNReal.toReal 2 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  refine hcol.congr fun n => ?_
  rw [hk.herm n k, RCLike.norm_conj]
