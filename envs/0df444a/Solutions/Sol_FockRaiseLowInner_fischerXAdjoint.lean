-- Prove2me | solution 1 for FockRaiseLowInner.fischerXAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:40:59.222855+00:00
-- url     : https://prove2.me/submissions/649d924f-47ae-4f4f-81d3-a85447b3a7f7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Theorems.Thm_FockRaiseLowInner_fockInner_X_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockRaiseLowInner
open MvPolynomial FockH1Action
variable {σ : Type*}
namespace FockRaiseLowInner
theorem _root_.solution : FockRL.FockXAdj := by
  intro τ l P Q
  exact fockInner_X_mul l P Q
end FockRaiseLowInner
