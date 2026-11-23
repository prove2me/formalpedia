-- Prove2me | solution 1 for DensInertW.valN_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:15.485612+00:00
-- url     : https://prove2.me/submissions/eb41f2b2-2b2b-40a4-9bdc-0bafd631a4d3

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
    valN q (d + 1) + q * valN q d = ((q : ℤ) + 1) * ((q : ℤ) ^ 2) ^ d := by
  unfold valN
  cases d with
  | zero => norm_num
  | succ d =>
    rw [show d + 1 + 1 - 1 = d + 1 by omega, show d + 1 - 1 = d by omega]
    ring
end DensInertW
