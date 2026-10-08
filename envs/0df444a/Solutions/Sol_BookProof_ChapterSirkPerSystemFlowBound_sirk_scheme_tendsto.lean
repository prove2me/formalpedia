-- Prove2me | solution 1 for BookProof.ChapterSirkPerSystemFlowBound.sirk_scheme_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T01:04:57.648759+00:00
-- url     : https://prove2.me/submissions/562ce9a8-6aaa-4840-a6b4-e093273bd5a4

-- Generated from ChapterSirkPerSystemFlowBound.lean — solution of BookProof.ChapterSirkPerSystemFlowBound.sirk_scheme_tendsto
import Mathlib
import Definitions.Def_ChapterSirkPerSystemFlowBound
import Theorems.Thm_BookProof_ChapterSirkPerSystemFlowBound_sirk_scheme_bound
import Theorems.Thm_BookProof_ChapterSirkEndToEnd_tendsto_zero_of_le_sirkBound
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
theorem solution {X : E →L[ℂ] E} {S : Set ℂ} {C Dmin h : ℝ} (hh : 0 < h)
    (hS : numRange X ⊆ S)
    {Gm : ℕ → Type*} [∀ m, NormedAddCommGroup (Gm m)] [∀ m, InnerProductSpace ℂ (Gm m)]
    [∀ m, CompleteSpace (Gm m)]
    (V : ∀ m, Gm m →L[ℂ] E) (s : ∀ m, RationalScheme E (Gm m))
    (hs : ∀ m, IsSirkScheme X (V m) S C Dmin h m (s m))
    (flow : E →L[ℂ] E) (hflow : ∀ m, flow = (s m).psiX) (v : E)
    (hv : ∀ m, V m ((V m).adjoint v) = v) :
    Tendsto (fun m => ‖flow v - sirkApprox (V m) (s m).psiB v‖) atTop (𝓝 0) :=
  tendsto_zero_of_le_sirkBound _ C Dmin h ‖v‖ hh (fun _ => norm_nonneg _)
      (fun m => sirk_scheme_bound (hs m) hS flow (hflow m) v (hv m))
