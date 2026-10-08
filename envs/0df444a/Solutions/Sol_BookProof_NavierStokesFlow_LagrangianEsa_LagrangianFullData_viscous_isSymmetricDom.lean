-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.viscous_isSymmetricDom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:30:00.630506+00:00
-- url     : https://prove2.me/submissions/f1e4edb8-150c-486e-b53a-c3ec7ae6c905

-- Generated from ChapterNavierStokesLagrangianEsa.lean — solution of BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.viscous_isSymmetricDom
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_LagrangianFullData_isSymmetricDom_sq
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_IsSymmetricDom_sum
import Theorems.Thm_BookProof_YangMillsHermite_PolySym_real_smul
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa
open BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData





open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

set_option maxHeartbeats 1000000 in
theorem solution : IsSymmetricDom L.viscous :=
  IsSymmetricDom.real_smul
      (IsSymmetricDom.sum Finset.univ fun i _ => isSymmetricDom_sq (L.Q_symm i)) _
