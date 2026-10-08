-- Prove2me | solution 1 for BookProof.ChapterSirkPerSystemFlowBound.norm_adjoint_apply_le_of_isometry
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T01:03:32.641247+00:00
-- url     : https://prove2.me/submissions/690dd1b6-eb15-4980-a7bc-230267d1ba84

-- Generated from ChapterSirkPerSystemFlowBound.lean — solution of BookProof.ChapterSirkPerSystemFlowBound.norm_adjoint_apply_le_of_isometry
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
theorem solution (V : G →L[ℂ] E) (hV : ∀ x : G, ‖V x‖ = ‖x‖)
    (v : E) : ‖V.adjoint v‖ ≤ ‖v‖ := by

  have hop : ‖V‖ ≤ 1 := V.opNorm_le_bound zero_le_one (fun x => by rw [hV]; simp)
  have hadj : ‖V.adjoint‖ = ‖V‖ := LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint V
  calc ‖V.adjoint v‖ ≤ ‖V.adjoint‖ * ‖v‖ := V.adjoint.le_opNorm v
    _ ≤ 1 * ‖v‖ := by rw [hadj]; exact mul_le_mul_of_nonneg_right hop (norm_nonneg _)
    _ = ‖v‖ := one_mul _
