-- Prove2me | solution 1 for FockRaiseLowInner.fischerConjLinearLeft
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:05.711859+00:00
-- url     : https://prove2.me/submissions/4bb58427-98f5-4da3-a282-926b0b2eea2e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Theorems.Thm_FockRaiseLowInner_fockInner_add_left
import Theorems.Thm_FockRaiseLowInner_fockInner_smul_left

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
theorem _root_.solution : FockRL.FockLinL := by
  intro τ c P₁ P₂ Q
  rw [fockInner_add_left, fockInner_smul_left]
end FockRaiseLowInner
