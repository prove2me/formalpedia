-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.bge_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:27:22.767418+00:00
-- url     : https://prove2.me/submissions/67e6c827-3ddd-4c80-b8d6-c4b05b6d60c7

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_zero__d9b99f199353
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_sub_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
variable (v : AddValuation K (WithTop ℚ)) {σ : Type}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (a : ℝ) (F : MvPolynomial σ K) :
    bge v a F ↔ ((a : ℝ) : WithTop ℝ) ≤ vBB v F := by
  unfold bge vBB
  rw [Finset.le_inf_iff]
  constructor
  · intro h α _
    exact (vge_sub_iff v a _ _).mp (h α)
  · intro h α
    by_cases hα : α ∈ F.support
    · exact (vge_sub_iff v a _ _).mpr (h α hα)
    · rw [notMem_support_iff.mp hα]; exact vge_zero' v _
end Formalism.MainNotions.PlaneGram
