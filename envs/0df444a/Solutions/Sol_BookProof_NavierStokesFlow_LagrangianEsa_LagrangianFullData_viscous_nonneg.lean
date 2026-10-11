-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.viscous_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:19:53.471154+00:00
-- url     : https://prove2.me/submissions/af27853c-7c82-4734-8fd8-4c724e9404c2

-- Generated from ChapterNavierStokesLagrangianEsa.lean — solution of BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.viscous_nonneg
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_LagrangianFullData_viscous_inner
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData





open FullEsa
open BookProof.BRSTNilpotent
open BookProof.NavierStokesFlow.LagrangianEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

set_option maxHeartbeats 1000000 in

theorem solution (v : L.D) : 0 ≤ (inner ℂ (v : F) (L.viscous v : F) : ℂ).re := by
  rw [L.viscous_inner v, Complex.ofReal_re]
  have h : (0 : ℝ) ≤ ∑ i : Fin 3, ‖(L.Q i v : F)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  exact mul_nonneg L.nu_nonneg h

/-! ### Criteria for essential self-adjointness -/
