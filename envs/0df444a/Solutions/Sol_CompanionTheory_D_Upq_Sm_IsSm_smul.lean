-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.IsSm.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:43:38.393971+00:00
-- url     : https://prove2.me/submissions/895f389b-a17b-4e2e-86b1-83eb65c563ed

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_clm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
namespace CompanionTheory.D.Upq.Sm
namespace IsSm
theorem _root_.solution {v : H} (hv : IsSm G σ v) (c : ℂ) : IsSm G σ (c • v) :=
  (SmOn.clm hv ((c • ContinuousLinearMap.id ℂ H).restrictScalars ℝ)).congr fun _ _ => by simp
end IsSm
end CompanionTheory.D.Upq.Sm
