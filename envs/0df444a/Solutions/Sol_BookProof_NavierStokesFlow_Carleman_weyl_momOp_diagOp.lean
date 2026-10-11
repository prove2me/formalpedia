-- Prove2me | solution 1 for BookProof.NavierStokesFlow.Carleman.weyl_momOp_diagOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:06:51.127432+00:00
-- url     : https://prove2.me/submissions/672b9374-4094-4239-b7c3-7d60c7e330ea

-- Generated from ChapterNavierStokesCarleman.lean — solution of BookProof.NavierStokesFlow.Carleman.weyl_momOp_diagOp
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman



open scoped ENNReal



open LpNat DiagonalEsa FullEsa

set_option maxHeartbeats 1000000 in
theorem solution (a : ℕ → ℝ) :
    momOp.comp (diagOp a) + (diagOp a).comp momOp = tridiagOp (nsCoupling a) := by

  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  cases n with
  | zero =>
      simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.coe_add, lp.coeFn_add,
        Pi.add_apply, momOp, tridiagOp_coe, diagOp_coe, tridiagFun, diagFun, nsCoupling]
      ring
  | succ m =>
      simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.coe_add, lp.coeFn_add,
        Pi.add_apply, momOp, tridiagOp_coe, diagOp_coe, tridiagFun, diagFun, nsCoupling,
        map_mul, map_neg, map_div₀, Complex.conj_I, Complex.conj_ofNat, Complex.conj_ofReal,
        map_add]
      ring
