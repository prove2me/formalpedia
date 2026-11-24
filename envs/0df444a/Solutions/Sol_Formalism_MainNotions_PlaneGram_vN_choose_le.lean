-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vN_choose_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:08:19.719961+00:00
-- url     : https://prove2.me/submissions/d026a1e4-6d8e-4b90-a828-86070fdfb889

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vN_eq

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
theorem _root_.solution (hD : DVRHyp v p) (n k : ℕ) : vN v (n.choose k) ≤ Nat.log p n := by
  rw [vN_eq hD]
  have := @Nat.factorization_choose_le_log p n k
  rw [Nat.factorization_def _ hD.prime] at this
  exact_mod_cast this
end Formalism.MainNotions.PlaneGram
