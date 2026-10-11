-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.drift_isSymmetricDom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:19:50.058071+00:00
-- url     : https://prove2.me/submissions/f04bd5a1-1494-4538-b1cd-1bc49a8586c0

-- Generated from ChapterNavierStokesLagrangianEsa.lean — solution of BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.drift_isSymmetricDom
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_IsSymmetricDom_sum
import Theorems.Thm_BookProof_YangMillsHermite_PolySym_real_smul
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData





open FullEsa
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.NavierStokesFlow.LagrangianEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

set_option maxHeartbeats 1000000 in

theorem solution : IsSymmetricDom L.drift :=
  IsSymmetricDom.sum Finset.univ fun i _ => (L.drive_symm i).real_smul _
