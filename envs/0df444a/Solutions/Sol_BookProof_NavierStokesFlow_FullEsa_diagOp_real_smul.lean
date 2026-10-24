-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.diagOp_real_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-23T16:57:13.337977+00:00
-- url     : https://prove2.me/submissions/d75b7b86-d0c3-43d7-85a2-28bbbfd5f314

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.diagOp_real_smul
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

theorem solution (r : ℝ) (a : ℕ → ℝ) :
    ((r : ℂ)) • diagOp a = diagOp (fun n => r * a n) := by
  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  simp only [LinearMap.smul_apply, Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, diagOp_coe, diagFun, Complex.ofReal_mul]
  ring
