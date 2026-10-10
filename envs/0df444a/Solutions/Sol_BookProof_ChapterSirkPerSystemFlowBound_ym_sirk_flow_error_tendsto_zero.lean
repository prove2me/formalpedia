-- Prove2me | solution 1 for BookProof.ChapterSirkPerSystemFlowBound.ym_sirk_flow_error_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:16:18.038126+00:00
-- url     : https://prove2.me/submissions/64470e48-c1fd-4d8e-931e-48c7e3c6c9a5

-- Generated from ChapterSirkPerSystemFlowBound.lean — solution of BookProof.ChapterSirkPerSystemFlowBound.ym_sirk_flow_error_tendsto_zero
import Mathlib
import Definitions.Def_ChapterSirkPerSystemFlowBound
import Theorems.Thm_BookProof_ChapterSirkPerSystemFlowBound_sirk_scheme_tendsto
import Theorems.Thm_BookProof_ChapterSirkPerSystem_ym_sirk_crouzeix_domain
open BookProof.ChapterSirkPerSystemFlowBound



noncomputable section

open Filter Topology


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH9
open BookProof.ChapterSirkEndToEnd BookProof.ChapterSirkSpectralGeometry
open BookProof.ChapterSirkPerSystem
open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.EsaClosure
open BookProof.YangMillsFriedrichs BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.Starobinsky
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.NSHashimoto
open BookProof.NavierStokesFlow.DiffHashimoto BookProof.NavierStokesFlow.DifferentialL2
open BookProof.NavierStokesFlow.LagrangianEsa BookProof.NavierStokesFlow.LagrangianKatoRellich

variable {E G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable {E G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

set_option maxHeartbeats 1000000 in
theorem solution (e : ℕ ≃ (Fin 99 →₀ ℕ))
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ (L2d 99)) (A : Dom →ₗ[ℂ] L2d 99) (R : L2d 99 →L[ℂ] L2d 99),
      IsPositiveSelfAdjointExtension (ymHamiltonian (coreRepBasis e) fabc) A ∧
        IsShiftInvert A γ R ∧ numRange R ⊆ realSegment 0 γ⁻¹ ∧
        ∀ (V : ∀ m : ℕ, EuclideanSpace ℂ (Fin m) →L[ℂ] L2d 99)
          (s : ∀ m : ℕ, RationalScheme (L2d 99) (EuclideanSpace ℂ (Fin m))) (C Dmin h : ℝ),
          0 < h →
          (∀ m, IsSirkScheme R (V m) (realSegment 0 γ⁻¹) C Dmin h m (s m)) →
          ∀ (flow : L2d 99 →L[ℂ] L2d 99), (∀ m, flow = (s m).psiX) →
          ∀ v : L2d 99, (∀ m, V m ((V m).adjoint v) = v) →
            Tendsto (fun m => ‖flow v - sirkApprox (V m) (s m).psiB v‖) atTop (𝓝 0) := by

  obtain ⟨Dom, A, R, hpsa, hR, -, hseg, -⟩ := ym_sirk_crouzeix_domain e fabc hγ
  exact ⟨Dom, A, R, hpsa, hR, hseg,
    fun V s _ _ _ hh hs flow hflow v hv => sirk_scheme_tendsto hh hseg V s hs flow hflow v hv⟩
