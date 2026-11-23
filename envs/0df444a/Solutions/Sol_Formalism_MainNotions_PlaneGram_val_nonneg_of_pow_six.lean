-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.val_nonneg_of_pow_six
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:32.937912+00:00
-- url     : https://prove2.me/submissions/4f625cd9-b8b1-4cfe-8c8d-e1cf6053fe19

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_val_of_le_pow_six

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
theorem _root_.solution (x : K) (n : ℕ) (h : ((n : ℕ) : WithTop ℚ) ≤ v (x ^ 6)) : 0 ≤ v x := by
  have h0 := le_val_of_le_pow_six x 0 n (by omega) h
  simpa using h0
end Formalism.MainNotions.PlaneGram
