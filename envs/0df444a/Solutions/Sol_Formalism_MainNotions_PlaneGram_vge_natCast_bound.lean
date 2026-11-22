-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vge_natCast_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:36.404797+00:00
-- url     : https://prove2.me/submissions/8b68b136-558c-4c69-a4e2-3a3211b7c5ec

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_rat_iff

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
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (c : ℕ) (x : K) : vge v (c : ℝ) x ↔ ((c : ℕ) : WithTop ℚ) ≤ v x := by
  have := vge_rat_iff v (c : ℚ) x
  simpa using this
end Formalism.MainNotions.PlaneGram
