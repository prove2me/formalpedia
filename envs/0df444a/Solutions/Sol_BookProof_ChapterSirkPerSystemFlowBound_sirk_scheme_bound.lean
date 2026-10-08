-- Prove2me | solution 1 for BookProof.ChapterSirkPerSystemFlowBound.sirk_scheme_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T01:04:42.297812+00:00
-- url     : https://prove2.me/submissions/1081b5c3-6ad0-4530-8992-33b669bbf8c9

-- Generated from ChapterSirkPerSystemFlowBound.lean — solution of BookProof.ChapterSirkPerSystemFlowBound.sirk_scheme_bound
import Mathlib
import Definitions.Def_ChapterSirkPerSystemFlowBound
import Theorems.Thm_BookProof_ChapterSirkPerSystemFlowBound_adjoint_comp_self_of_isometry
import Theorems.Thm_BookProof_ChapterSirkPerSystemFlowBound_norm_adjoint_apply_le_of_isometry
import Theorems.Thm_BookProof_ChapterSirkSpectralGeometry_sirk_end_to_end_crouzeix_domain
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
theorem solution {X : E →L[ℂ] E} {V : G →L[ℂ] E} {S : Set ℂ} {C Dmin h : ℝ} {m : ℕ}
    {s : RationalScheme E G} (hs : IsSirkScheme X V S C Dmin h m s) (hS : numRange X ⊆ S)
    (flow : E →L[ℂ] E) (hflow : flow = s.psiX) (v : E) (hv : V (V.adjoint v) = v) :
    ‖flow v - sirkApprox V s.psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m :=
  sirk_end_to_end_crouzeix_domain V X s.qX s.qXinv s.qBinv s.p flow s.psiX s.psiB
      C Dmin h m S hS (adjoint_comp_self_of_isometry V hs.iso) hs.iso
      (norm_adjoint_apply_le_of_isometry V hs.iso) hs.invX hs.invq hs.qXl hs.qBr hflow
      hs.cxX hs.cxB v hv
