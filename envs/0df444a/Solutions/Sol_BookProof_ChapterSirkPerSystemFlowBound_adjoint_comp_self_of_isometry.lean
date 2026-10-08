-- Prove2me | solution 1 for BookProof.ChapterSirkPerSystemFlowBound.adjoint_comp_self_of_isometry
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T01:03:17.104765+00:00
-- url     : https://prove2.me/submissions/f04695df-4f1c-429f-b896-5dd1cb52238a

-- Generated from ChapterSirkPerSystemFlowBound.lean — solution of BookProof.ChapterSirkPerSystemFlowBound.adjoint_comp_self_of_isometry
import Mathlib
import Definitions.Def_ChapterSirkPerSystemFlowBound
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
theorem solution (V : G →L[ℂ] E) (hV : ∀ x : G, ‖V x‖ = ‖x‖) :
    V.adjoint.comp V = ContinuousLinearMap.id ℂ G := by

  set Vi : G →ₗᵢ[ℂ] E := { toLinearMap := V.toLinearMap, norm_map' := hV } with hVi
  have hinner : ∀ a b : G, (inner ℂ (V a) (V b) : ℂ) = inner ℂ a b :=
    fun a b => Vi.inner_map_map a b
  ext x
  refine ext_inner_right ℂ ?_
  intro y
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
  simpa using hinner x y
