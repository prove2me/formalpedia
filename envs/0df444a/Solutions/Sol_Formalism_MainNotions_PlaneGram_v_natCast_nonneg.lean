-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.v_natCast_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:32.223185+00:00
-- url     : https://prove2.me/submissions/9630d805-15d9-4199-a713-596fe43599af

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
theorem _root_.solution (n : ℕ) : 0 ≤ v (n : K) := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact le_trans (le_min ih (by simp)) (v.map_add _ _)
end Formalism.MainNotions.PlaneGram
