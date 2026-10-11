-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_isSymmetricDom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:19:49.037013+00:00
-- url     : https://prove2.me/submissions/e1783453-1f8d-470b-b860-1bd6f6cad8e2

-- Generated from ChapterNavierStokesLagrangianEsa.lean — solution of BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_isSymmetricDom
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_LagrangianFullData_isSymmetricDom_sq
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_IsSymmetricDom_sum
import Theorems.Thm_BookProof_YangMillsHermite_PolySym_real_smul
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData





open FullEsa
open BookProof.ChapterF7
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.NavierStokesFlow.LagrangianEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

set_option maxHeartbeats 1000000 in

theorem solution : IsSymmetricDom L.kinetic :=
  IsSymmetricDom.real_smul
    (IsSymmetricDom.sum Finset.univ fun i _ => isSymmetricDom_sq (L.P_symm i)) _
