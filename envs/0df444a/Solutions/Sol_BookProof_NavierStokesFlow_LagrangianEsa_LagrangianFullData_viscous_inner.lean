-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.viscous_inner
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:19:52.488294+00:00
-- url     : https://prove2.me/submissions/36e9a482-fd9a-4880-be40-503d48672f69

-- Generated from ChapterNavierStokesLagrangianEsa.lean — solution of BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.viscous_inner
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_LagrangianFullData_inner_comp_self
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

theorem solution (v : L.D) :
    (inner ℂ (v : F) (L.viscous v : F) : ℂ)
      = ((L.nu * ∑ i : Fin 3, ‖(L.Q i v : F)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [viscous, LinearMap.smul_apply, LinearMap.sum_apply, Submodule.coe_smul,
    Submodule.coe_sum, inner_smul_right, inner_sum, Complex.ofReal_mul, Complex.ofReal_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => inner_comp_self (L.Q_symm i) v
