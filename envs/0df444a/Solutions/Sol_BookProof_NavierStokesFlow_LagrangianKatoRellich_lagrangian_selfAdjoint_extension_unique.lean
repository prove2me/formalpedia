-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_selfAdjoint_extension_unique
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T07:54:10.10398+00:00
-- url     : https://prove2.me/submissions/7f9e1718-177d-4173-9185-93d51b043aa2

-- Generated from ChapterNavierStokesLagrangianKatoRellich.lean — solution of BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_selfAdjoint_extension_unique
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesLagrangianEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianKatoRellich

















open Filter Topology



open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LagrangianEsa BookProof.FarisLavine
open BookProof.EsaClosure BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)


























variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (L : LagrangianFullData F)

set_option maxHeartbeats 1000000 in
theorem solution
    (hesa : EssentiallySelfAdjointOn L.D (lagrangianCore L))
    {Dom₁ Dom₂ : Submodule ℂ F} {A₁ : Dom₁ →ₗ[ℂ] F} {A₂ : Dom₂ →ₗ[ℂ] F}
    (h₁ : IsSelfAdjointExtension (lagrangianCore L) A₁)
    (h₂ : IsSelfAdjointExtension (lagrangianCore L) A₂) :
    Dom₁ = Dom₂ ∧ ∀ (x : F) (h : x ∈ Dom₁) (h' : x ∈ Dom₂), A₁ ⟨x, h⟩ = A₂ ⟨x, h'⟩ := isSelfAdjointExtension_unique_of_esa hesa h₁ h₂
