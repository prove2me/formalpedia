-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.kapL_term_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:17.082142+00:00
-- url     : https://prove2.me/submissions/b6b394d2-75bd-4e90-a45d-55496d6f7d91

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_logb_add_nonneg

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
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (r a : ℕ) :
    0 ≤ (if a = 0 then 0 else (r : ℝ) * Real.logb p ((a : ℝ) + r)) := by
  split_ifs with ha
  · exact le_refl 0
  · exact mul_nonneg (Nat.cast_nonneg r) (logb_add_nonneg hp r a (by omega))
end Formalism.MainNotions.PlaneGram
