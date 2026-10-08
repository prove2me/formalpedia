-- Prove2me | solution 1 for BookProof.ChapterSirkPerSystemFlowBound.ym_sirk_flow_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T01:05:13.284756+00:00
-- url     : https://prove2.me/submissions/b1865cfb-bd7f-48f7-a7b3-85155e07abe7

-- Generated from ChapterSirkPerSystemFlowBound.lean — solution of BookProof.ChapterSirkPerSystemFlowBound.ym_sirk_flow_error_bound
import Mathlib
import Definitions.Def_ChapterSirkPerSystemFlowBound
import Theorems.Thm_BookProof_ChapterSirkPerSystemFlowBound_sirk_scheme_bound
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
        IsShiftInvert A γ R ∧ IsSelfAdjoint R ∧
        numRange R ⊆ realSegment 0 γ⁻¹ ∧
        ∀ (m : ℕ) (V : EuclideanSpace ℂ (Fin m) →L[ℂ] L2d 99)
          (s : RationalScheme (L2d 99) (EuclideanSpace ℂ (Fin m))) (C Dmin h : ℝ),
          IsSirkScheme R V (realSegment 0 γ⁻¹) C Dmin h m s →
          ∀ (flow : L2d 99 →L[ℂ] L2d 99), flow = s.psiX →
          ∀ v : L2d 99, V (V.adjoint v) = v →
            ‖flow v - sirkApprox V s.psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m := by

  obtain ⟨Dom, A, R, hpsa, hR, hsa, hseg, -⟩ := ym_sirk_crouzeix_domain e fabc hγ
  exact ⟨Dom, A, R, hpsa, hR, hsa, hseg,
    fun _ _ _ _ _ _ hs flow hflow v hv => sirk_scheme_bound hs hseg flow hflow v hv⟩
