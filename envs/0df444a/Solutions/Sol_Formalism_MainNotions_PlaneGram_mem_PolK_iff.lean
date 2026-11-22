-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.mem_PolK_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:12:47.68245+00:00
-- url     : https://prove2.me/submissions/e687a3ea-c573-41fc-9c7f-116eb87944fa

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_LiftBoundOfHypotheses
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff

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
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {L : Type} {r : ℕ} (d : L → ℕ) (F : MvPolynomial (L × Fin r) K) :
    F ∈ PolK K r d ↔ ∀ α ∈ F.support, ∀ i, ldeg α i = d i := by
  simp only [PolK, mem_restrictSupport_iff, Set.subset_def, Finset.mem_coe, Set.mem_setOf_eq, ldeg]
end Formalism.MainNotions.PlaneGram
