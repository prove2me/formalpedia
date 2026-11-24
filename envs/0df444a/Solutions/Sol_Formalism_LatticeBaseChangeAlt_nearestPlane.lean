-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.nearestPlane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:50.886367+00:00
-- url     : https://prove2.me/submissions/69ff8ebf-e1a3-4a5f-83ba-dfa12039288e

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_TransvectionIsometry
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_ExistsSumOfMemSpanImage
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_nearestPlane_finset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Finset
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : NearestPlane := by
  unfold NearestPlane
  intro V _ _ n v _ x hx
  have hx' : x ∈ Submodule.span ℝ (v '' ((Finset.univ : Finset (Fin n)) : Set (Fin n))) := by
    rwa [Finset.coe_univ, Set.image_univ]
  exact nearestPlane_finset v Finset.univ x hx'
end Formalism.LatticeBaseChangeAlt
