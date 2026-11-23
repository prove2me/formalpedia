-- Prove2me | solution 1 for Formalism.FG.ShiftFEAux.pow_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:23:02.304267+00:00
-- url     : https://prove2.me/submissions/7cdc7b40-6d57-4f12-b33a-256ef049991a

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.FG
open Formalism.FG.ShiftFEAux
open MvPowerSeries
variable {K : Type*} [Field K] {l m : ℕ}
namespace Formalism.FG.ShiftFEAux
theorem _root_.solution (hl : 2 ≤ l) {a b : ℕ} (h : (l ^ 2) ^ a = (l ^ 2) ^ b) : a = b :=
  Nat.pow_right_injective (le_trans hl (Nat.le_self_pow two_ne_zero l)) h
end Formalism.FG.ShiftFEAux
