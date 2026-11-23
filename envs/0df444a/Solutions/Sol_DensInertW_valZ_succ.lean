-- Prove2me | solution 1 for DensInertW.valZ_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:15.921174+00:00
-- url     : https://prove2.me/submissions/72f44aef-e2e0-4678-b13e-4efcc7307818

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankValPerp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ValMain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
open DensInertW
namespace DensInertW
theorem _root_.solution (q d : ℕ) :
    valZ q (d + 1) + q * valZ q d = ((q : ℤ) + 1) * ((q : ℤ) ^ 2) ^ d := by
  unfold valZ
  cases d with
  | zero =>
    norm_num
    ring
  | succ d =>
    rw [show 2 * (d + 1 + 1) - 1 = 2 * d + 3 by omega, show d + 1 + 1 - 1 = d + 1 by omega,
      show 2 * (d + 1) - 1 = 2 * d + 1 by omega, show d + 1 - 1 = d by omega]
    ring
end DensInertW
