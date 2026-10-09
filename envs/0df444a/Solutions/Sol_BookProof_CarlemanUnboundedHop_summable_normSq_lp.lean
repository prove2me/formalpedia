-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.summable_normSq_lp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:00:59.649898+00:00
-- url     : https://prove2.me/submissions/e10e4ae3-8713-4d78-b772-88900b18b4ca

-- Generated from ChapterCarlemanUnboundedHop.lean — solution of BookProof.CarlemanUnboundedHop.summable_normSq_lp
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
import Definitions.Def_ChapterNavierStokesDeficiency
open BookProof.NavierStokesFlow.LpNat
open BookProof.CarlemanUnboundedHop




open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (f : L2N) : Summable fun n : ℕ => ‖(f : ℕ → ℂ) n‖ ^ 2 := by

  have hsum := (lp.memℓp f).summable (p := 2) (by norm_num)
  refine hsum.congr fun n => ?_
  rw [show ENNReal.toReal 2 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
