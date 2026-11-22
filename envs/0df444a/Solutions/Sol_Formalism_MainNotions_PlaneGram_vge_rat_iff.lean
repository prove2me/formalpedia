-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vge_rat_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:40.53896+00:00
-- url     : https://prove2.me/submissions/f1cd7893-1a91-482e-b7aa-9e93337e7915

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral

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
theorem _root_.solution (n : ℚ) (x : K) : vge v (n : ℝ) x ↔ (n : WithTop ℚ) ≤ v x := by
  unfold vge vR
  cases h : v x <;> simp
end Formalism.MainNotions.PlaneGram
