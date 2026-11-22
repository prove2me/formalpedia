-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.logb_add_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:32.261079+00:00
-- url     : https://prove2.me/submissions/27fc7b46-8647-41d5-b733-1956587dd643

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
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (r a : ℕ) (h : 1 ≤ a + r) :
    0 ≤ Real.logb p ((a : ℝ) + r) := by
  apply Real.logb_nonneg
  · exact_mod_cast (by omega : 1 < p)
  · exact_mod_cast h
end Formalism.MainNotions.PlaneGram
