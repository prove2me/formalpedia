-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.v_add_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:42.955753+00:00
-- url     : https://prove2.me/submissions/235ad27d-3de7-47ca-8978-8b8ff5f22c03

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
variable {v}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {x y : K} {c : WithTop ℚ} (hx : c ≤ v x) (hy : c ≤ v y) : c ≤ v (x + y) := by
  exact le_trans (le_min hx hy) (AddValuation.map_add v x y)
end Formalism.MainNotions.PlaneGram
