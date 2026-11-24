-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vge_p_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:32:33.495075+00:00
-- url     : https://prove2.me/submissions/6e8ef33f-7dbd-46de-ad68-8e207146e676

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_rat_iff
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_p_pow

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
variable {v} {p : ℕ} [CharZero K]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (hD : DVRHyp v p) (n : ℕ) : vge v (n : ℝ) ((p : K) ^ n) := by
  have := (vge_rat_iff v (n : ℚ) ((p : K) ^ n)).mpr (le_of_eq (v_p_pow hD n).symm)
  simpa using this
end Formalism.MainNotions.PlaneGram
