-- Prove2me | solution 1 for Formalism.FG.ShiftFEAux.map_shiftLog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:12.354395+00:00
-- url     : https://prove2.me/submissions/0ef45221-e488-47ce-bc11-b71e0316e518

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Theorems.Thm_Formalism_FG_ShiftFEAux_coeff_shiftLog

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
theorem _root_.solution (σ : K →+* K) (k : ZMod m) :
    map σ (shiftLog K l m k) = shiftLog K l m k := by
  ext n
  rw [coeff_map, coeff_shiftLog, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp [map_inv₀]
end Formalism.FG.ShiftFEAux
