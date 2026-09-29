-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianKatoRellich.diagKR_hFull_hasZeroDeficiencyOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:45:01.612109+00:00
-- url     : https://prove2.me/submissions/ca407124-1e3c-421e-b8cc-68027c0da4b5

-- Generated from ChapterNavierStokesLagrangianKatoRellich.lean — solution of BookProof.NavierStokesFlow.LagrangianKatoRellich.diagKR_hFull_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianKatoRellich_hFull_hasZeroDeficiencyOn_of_drive_eq_P
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianKatoRellich_diagKR_drive
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianKatoRellich_diagKR_constraint_bound
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianKatoRellich_diagKR_secondOrder_hasZeroDeficiencyOn
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterNavierStokesDeficiency
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianKatoRellich

















open Filter Topology



open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LagrangianEsa BookProof.FarisLavine
open BookProof.EsaClosure BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)


























variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (L : LagrangianFullData F)








open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.DiagonalEsa

set_option maxHeartbeats 1000000 in
theorem solution :
    HasZeroDeficiencyOn diagKR.D diagKR.hFull :=
  hFull_hasZeroDeficiencyOn_of_drive_eq_P diagKR diagKR_drive le_rfl diagKR_constraint_bound
      diagKR_secondOrder_hasZeroDeficiencyOn
