-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.diagOp_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-23T17:02:33.708648+00:00
-- url     : https://prove2.me/submissions/515d7014-1598-4ea9-9c27-436b0f0d6767

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.diagOp_sum
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_diagOp_add
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa



open scoped ENNReal
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.NavierStokesFlow.DiagonalEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

set_option maxHeartbeats 1000000 in
theorem solution {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℝ) :
    (∑ i ∈ s, diagOp (a i)) = diagOp (fun n => ∑ i ∈ s, a i n) := by

  classical
  induction s using Finset.induction with
  | empty =>
      refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
      funext n
      simp [diagFun]
  | insert x s hx ih =>
      rw [Finset.sum_insert hx, ih, diagOp_add]
      congr 1
      funext n
      rw [Finset.sum_insert hx]
