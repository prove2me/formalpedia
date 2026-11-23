-- Prove2me | solution 1 for Formalism.FG.ShiftFEAux.eq_zero_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:34.625063+00:00
-- url     : https://prove2.me/submissions/1aa3668a-9c17-41fd-b64a-6bcb965475d0

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Theorems.Thm_Formalism_FG_ShiftFEAux_pow_inj

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
theorem _root_.solution (hl : 2 ≤ l) {a : ℕ} (h : (l ^ 2) ^ a = 1) : a = 0 :=
  pow_inj hl (h.trans (pow_zero _).symm)
end Formalism.FG.ShiftFEAux
