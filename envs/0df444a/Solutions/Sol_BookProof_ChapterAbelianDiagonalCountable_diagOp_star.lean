-- Prove2me | solution 1 for BookProof.ChapterAbelianDiagonalCountable.diagOp_star
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:49:16.152+00:00
-- url     : https://prove2.me/submissions/7e6ca221-eb96-452b-9810-8190e052c0a9

-- Generated from ChapterAbelianDiagonalCountable.lean — solution of BookProof.ChapterAbelianDiagonalCountable.diagOp_star
import Mathlib
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable



open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in

@[simp] private theorem diagOp_apply (d : EllInf) (f : Ell2C) (i : ℕ) :
    ((diagOp d f : Ell2C) : ℕ → ℂ) i = (d : ℕ → ℂ) i * (f : ℕ → ℂ) i := rfl

theorem solution (d : EllInf) (f g : Ell2C) :
    (inner ℂ (diagOp d f) g : ℂ) = inner ℂ f (diagOp (star d) g) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  simp [RCLike.inner_apply, map_mul, mul_comm, mul_left_comm]
