-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.hasWt_add_pow_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:07:16.910827+00:00
-- url     : https://prove2.me/submissions/2939f33f-2d51-4616-b0af-4a6ff8070677

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_IdentityTwentyB
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Theorems.Thm_Formalism_BaseCaseIdentities_hasWt_add_pow_sub_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
variable {k : Type*} [Field k] {Z : Type*} {v : AddValuation k (WithTop ℝ)}
  {r w w' w1 w2 wa wb a₀ : ℝ} {f g a b : MvPowerSeries Z k}
namespace Formalism.BaseCaseIdentities
theorem _root_.solution {l e : ℕ} (hl : l.Prime) (hv : v (l : k) = 1) (hw : wa ≤ wb)
    (ha : HasWt v r wa a) (hb : HasWt v r wb b) :
    HasWt v r (1 + (((l ^ e : ℕ) : ℝ) - 1) * wa + wb)
      ((a + b) ^ (l ^ e) - a ^ (l ^ e) - b ^ (l ^ e)) :=
  hasWt_add_pow_sub_pow hv (Nat.one_le_pow _ _ hl.pos)
    (fun m h0 h1 => hl.dvd_choose_pow (by omega) (by omega)) hw ha hb
end Formalism.BaseCaseIdentities
