-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_nonneg
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:36:03.10984+00:00
-- url     : https://prove2.me/submissions/a202164a-7a18-4a0e-ad8f-52b0bc706a1e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — solution of BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_nonneg
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_LagrangianFullData_kinetic_inner
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData





open FullEsa
open BookProof.ChapterF7
open BookProof.NavierStokesFlow.LagrangianEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

set_option maxHeartbeats 1000000 in

theorem solution (v : L.D) : 0 ≤ (inner ℂ (v : F) (L.kinetic v : F) : ℂ).re := by
  rw [L.kinetic_inner v, Complex.ofReal_re]
  have : (0 : ℝ) ≤ ∑ i : Fin 3, ‖(L.P i v : F)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith
