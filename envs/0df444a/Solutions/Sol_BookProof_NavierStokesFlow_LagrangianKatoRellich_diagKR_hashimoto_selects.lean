-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianKatoRellich.diagKR_hashimoto_selects
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:45:00.390283+00:00
-- url     : https://prove2.me/submissions/ea286563-1f9a-4386-b81f-80684d61f565

-- Generated from ChapterNavierStokesLagrangianKatoRellich.lean — solution of BookProof.NavierStokesFlow.LagrangianKatoRellich.diagKR_hashimoto_selects
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianKatoRellich_lagrangian_hashimoto_selects
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianKatoRellich_diagKR_hFull_essentiallySelfAdjointOn
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
theorem solution (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) :
    ∃ (Dom : Submodule ℂ L2N) (A : Dom →ₗ[ℂ] L2N) (X : ℕ → L2N →L[ℂ] L2N),
      IsSelfAdjointExtension (lagrangianCore diagKR) A ∧
      (∀ j, IsShiftInvertC A (γ j) (X j)) ∧
      (∀ j, ‖X j‖ ≤ |(γ j).im|⁻¹) ∧
      (∀ j, Dom = LinearMap.range ((X j : L2N →ₗ[ℂ] L2N))) ∧
      (∀ j k u, X j u - X k u = (γ k - γ j) • X j (X k u)) ∧
      (∀ j k, X j ∘L X k = X k ∘L X j) ∧
      (∀ j m, X j ∘L (ContinuousLinearMap.id ℂ L2N - (γ m - γ j) • X m) = X m) ∧
      (∀ m v k, sirkDen (X m) (fun i => γ m - γ i) k (rkVec X v k) = (X m ^ k) v) ∧
      (∀ j u, Tendsto (fun n : ℕ => galerkinCompression (X j) l2NatBasis n u) atTop
        (nhds (X j u))) ∧
      (∀ j (Dom' : Submodule ℂ L2N) (A' : Dom' →ₗ[ℂ] L2N), IsShiftInvertC A' (γ j) (X j) →
        Dom' = Dom ∧ ∀ (x : L2N) (hx : x ∈ Dom) (hx' : x ∈ Dom'), A' ⟨x, hx'⟩ = A ⟨x, hx⟩) := lagrangian_hashimoto_selects diagKR diagKR_hFull_essentiallySelfAdjointOn l2NatBasis γ hγ
