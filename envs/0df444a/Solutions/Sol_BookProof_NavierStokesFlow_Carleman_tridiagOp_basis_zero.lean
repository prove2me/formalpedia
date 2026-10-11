-- Prove2me | solution 1 for BookProof.NavierStokesFlow.Carleman.tridiagOp_basis_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:05:59.004191+00:00
-- url     : https://prove2.me/submissions/26982416-d6a4-4eb9-bf1f-034df1be4eab

-- Generated from ChapterNavierStokesCarleman.lean — solution of BookProof.NavierStokesFlow.Carleman.tridiagOp_basis_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman



open scoped ENNReal



open LpNat DiagonalEsa FullEsa

set_option maxHeartbeats 1000000 in
theorem solution (c : ℕ → ℂ) :
    ((tridiagOp c (basis 0) : lpFiniteModes ℕ) : L2N)
      = (starRingEnd ℂ (c 0)) • lp.single 2 1 (1 : ℂ) := by

  ext m
  cases m with
  | zero => simp [tridiagOp, basis, tridiagFun, lp.single_apply]
  | succ j =>
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      simp [tridiagOp, basis, tridiagFun, lp.single_apply]
    · have hj1 : j ≠ 0 := by omega
      simp [tridiagOp, basis, tridiagFun, lp.single_apply, hj1]
