-- Prove2me | solution 1 for BookProof.NavierStokesFlow.Carleman.summable_mul_shift
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:06:33.495156+00:00
-- url     : https://prove2.me/submissions/a10d934e-8985-4422-b4f7-c6bb1a334d78

-- Generated from ChapterNavierStokesCarleman.lean — solution of BookProof.NavierStokesFlow.Carleman.summable_mul_shift
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Theorems.Thm_BookProof_NavierStokesFlow_Carleman_summable_normSq
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman



open scoped ENNReal



open LpNat DiagonalEsa FullEsa

set_option maxHeartbeats 1000000 in
theorem solution (w : L2N) :
    Summable fun n : ℕ => ‖(w : ℕ → ℂ) n‖ * ‖(w : ℕ → ℂ) (n + 1)‖ := by

  have hsq := summable_normSq w
  have hshift : Summable fun n : ℕ => ‖(w : ℕ → ℂ) (n + 1)‖ ^ 2 :=
    (summable_nat_add_iff 1).2 hsq
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (((hsq.add hshift)).mul_left (1 / 2))
  have h := sq_nonneg (‖(w : ℕ → ℂ) n‖ - ‖(w : ℕ → ℂ) (n + 1)‖)
  nlinarith [h]
