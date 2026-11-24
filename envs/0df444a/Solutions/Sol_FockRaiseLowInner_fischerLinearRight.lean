-- Prove2me | solution 1 for FockRaiseLowInner.fischerLinearRight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:08.211152+00:00
-- url     : https://prove2.me/submissions/16de93a4-2352-4ebe-8bcb-e9faf9ad0120

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Theorems.Thm_FockRaiseLowInner_fockInner_add_right
import Theorems.Thm_FockRaiseLowInner_fockInner_smul_right

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
theorem _root_.solution : FockRL.FockLinR := by
  intro τ c P Q₁ Q₂
  rw [fockInner_add_right, fockInner_smul_right]
end FockRaiseLowInner
