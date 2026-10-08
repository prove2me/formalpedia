-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:07:08.088279+00:00
-- url     : https://prove2.me/submissions/e0c73875-5648-4e7d-89ab-204b503ec3c7

-- Generated from ChapterNavierStokesLagrangianEsa.lean — solution of BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_decomposition
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa
open BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData





open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

set_option maxHeartbeats 1000000 in
theorem solution :
    L.hFull = L.kinetic + L.viscous + L.drift + L.constraintOp := rfl
