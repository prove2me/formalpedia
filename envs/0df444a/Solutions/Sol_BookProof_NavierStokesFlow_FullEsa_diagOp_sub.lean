-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.diagOp_sub
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-23T16:57:14.431035+00:00
-- url     : https://prove2.me/submissions/db23c7d1-3531-45f2-971f-587cf332a091

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.diagOp_sub
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa



open scoped ENNReal
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.DiagonalEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

set_option maxHeartbeats 1000000 in

theorem solution (a b : ℕ → ℝ) : diagOp a - diagOp b = diagOp (fun n => a n - b n) := by
  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  simp only [LinearMap.sub_apply, Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, diagOp_coe,
    diagFun, Complex.ofReal_sub]
  ring
