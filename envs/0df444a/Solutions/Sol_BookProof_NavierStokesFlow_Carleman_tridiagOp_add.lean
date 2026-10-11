-- Prove2me | solution 1 for BookProof.NavierStokesFlow.Carleman.tridiagOp_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:06:35.734982+00:00
-- url     : https://prove2.me/submissions/bb906fcc-6b67-41c9-83cf-b88f54f361b4

-- Generated from ChapterNavierStokesCarleman.lean — solution of BookProof.NavierStokesFlow.Carleman.tridiagOp_add
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman



open scoped ENNReal



open LpNat DiagonalEsa FullEsa

set_option maxHeartbeats 1000000 in
theorem solution (c c' : ℕ → ℂ) :
    tridiagOp c + tridiagOp c' = tridiagOp (fun n => c n + c' n) := by

  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  cases n with
  | zero => simp only [LinearMap.add_apply, Submodule.coe_add, lp.coeFn_add, Pi.add_apply,
      tridiagOp_coe, tridiagFun]; ring
  | succ m => simp only [LinearMap.add_apply, Submodule.coe_add, lp.coeFn_add, Pi.add_apply,
      tridiagOp_coe, tridiagFun, map_add]; ring
